import ElementaryHolonics.Foundation.ReceiverHistoryCompression

/-!
# Traditional machine learning as a dynamic receiver chart

This file does not install a machine-learning ontology.  It states the exact conditions under
which a fixed labelled state machine is a receiver quotient of one holonic transport system.
Present observation factorization is insufficient: the quotient must commute with every native
generator.  The existing lineage theorem then carries the square through every ordered word.
-/

namespace Soma.Holonics.Computation.MachineLearningChart

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.LineageCompression

universe uG uR uH uC uF

/-!
The engine-facing existence criterion comes before a proposed classical transition.  A quotient
successor can be constructed on the actually presented quotient range exactly when the native
successor is constant on every complete quotient fibre.
-/

/-- The native successor returned over one proposed quotient face. -/
abbrev QuotientSuccessorTransformer
    {Native : Type uH} {Classical : Type uC}
    (quotient : Native → Classical) (nativeStep : Native → Native) :=
  ReceiverTransformer quotient (fun native => quotient (nativeStep native))

/-- Exact nonlinear descent criterion for one native generator. -/
theorem quotientSuccessorTransformer_exists_iff
    {Native : Type uH} {Classical : Type uC}
    (quotient : Native → Classical) (nativeStep : Native → Native) :
    Nonempty (QuotientSuccessorTransformer quotient nativeStep) ↔
      ∀ left right, quotient left = quotient right →
        quotient (nativeStep left) = quotient (nativeStep right) :=
  receiverTransformer_exists_iff quotient (fun native => quotient (nativeStep native))

/--
A fixed-carrier machine-learning chart over a native holonic carrier.

`nativeStep` is the productive transport. `classicalStep` is its proposed exterior fixed-state
presentation.  `quotient` is lawful only because both the observation and generator squares are
explicit fields.
-/
structure DynamicReceiverChart
    (Generator : Type uG) (Receiver : Type uR)
    (Native : Type uH) (Classical : Type uC) (Face : Type uF) where
  quotient : Native → Classical
  nativeStep : Generator → Native → Native
  classicalStep : Generator → Classical → Classical
  nativeObserve : Receiver → Native → Face
  classicalObserve : Receiver → Classical → Face
  observeExact : ∀ receiver native,
    classicalObserve receiver (quotient native) = nativeObserve receiver native
  generatorExact : ∀ generator native,
    quotient (nativeStep generator native) = classicalStep generator (quotient native)

namespace DynamicReceiverChart

variable {Generator : Type uG} {Receiver : Type uR}
  {Native : Type uH} {Classical : Type uC} {Face : Type uF}
  (C : DynamicReceiverChart Generator Receiver Native Classical Face)

/-- The present classical observation is an exact receiver quotient. -/
def presentCompression : Compression Receiver Native Classical Face where
  quotient := C.quotient
  receiver := C.nativeObserve
  factor := C.classicalObserve
  exact := C.observeExact

/-- The chart is a receiver-history compression, not merely a present observation map. -/
def historyCompression :
    ReceiverHistoryCompression Generator Receiver Native Classical Face where
  present := C.presentCompression
  sourceTransport := C.nativeStep
  quotientTransport := C.classicalStep
  generatorExact := C.generatorExact

/-- Every ordered native transition word projects to the corresponding classical word. -/
theorem everyOrderedWordExact (word : List Generator) (native : Native) :
    C.quotient (transportWord C.nativeStep word native) =
      transportWord C.classicalStep word (C.quotient native) :=
  C.historyCompression.quotientCommutesWithEveryOrderedWord word native

/-- Every declared receiver after every ordered word factors through the classical chart. -/
theorem everyReceiverHistoryExact (receiver : Receiver) (word : List Generator)
    (native : Native) :
    C.classicalObserve receiver
        (transportWord C.classicalStep word (C.quotient native)) =
      C.nativeObserve receiver (transportWord C.nativeStep word native) := by
  rw [← C.everyOrderedWordExact word native]
  exact C.observeExact receiver (transportWord C.nativeStep word native)

/-- One labelled deterministic step, presented relationally. -/
def nativeTransition (native : Native) (label : Generator) (successor : Native) : Prop :=
  C.nativeStep label native = successor

/-- The corresponding transition on the classical receiver chart. -/
def classicalTransition
    (classical : Classical) (label : Generator) (successor : Classical) : Prop :=
  C.classicalStep label classical = successor

/-- Generator descent is precisely a forward simulation under the quotient map. -/
theorem quotientIsForwardSimulation
    {native successor : Native} {label : Generator}
    (step : C.nativeTransition native label successor) :
    C.classicalTransition (C.quotient native) label (C.quotient successor) := by
  unfold nativeTransition at step
  unfold classicalTransition
  rw [← C.generatorExact label native, step]

/--
A reconstruction on an admitted native region.  This is stronger than surjectivity: it retains the
same native occurrence after quotient and reconstruction, and the region is closed under every
admitted generator.
-/
structure ReachableReconstruction (nativeRegion : Set Native) where
  reconstruct : Classical → Native
  reconstruct_quotient : ∀ native, native ∈ nativeRegion →
    reconstruct (C.quotient native) = native
  native_closed : ∀ generator native, native ∈ nativeRegion →
    C.nativeStep generator native ∈ nativeRegion

/-- On a reconstructed reachable region, every classical successor reconstructs to the native one. -/
theorem reconstructClassicalSuccessor
    {nativeRegion : Set Native} (R : C.ReachableReconstruction nativeRegion)
    (generator : Generator) (native : Native) (hnative : native ∈ nativeRegion) :
    R.reconstruct (C.classicalStep generator (C.quotient native)) =
      C.nativeStep generator native := by
  rw [← C.generatorExact generator native]
  exact R.reconstruct_quotient _ (R.native_closed generator native hnative)

/-- A future receiver/history separator proves that the classical chart did not identify the pair. -/
theorem separatingHistoryReopensClassicalFace {left right : Native}
    (receiver : Receiver) (word : List Generator)
    (separates :
      C.nativeObserve receiver (transportWord C.nativeStep word left) ≠
        C.nativeObserve receiver (transportWord C.nativeStep word right)) :
    C.quotient left ≠ C.quotient right :=
  C.historyCompression.separatingSuccessorReopensTheProposedQuotient receiver word separates

end DynamicReceiverChart

/-! ## Finite controls -/

namespace Control

/-- A lawful quotient: the hidden Boolean coordinate remains hidden under both generators. -/
def stableChart : DynamicReceiverChart Bool Unit (Bool × Bool) Bool Bool where
  quotient := Prod.fst
  nativeStep
    | false, state => state
    | true, (visible, hidden) => (!visible, hidden)
  classicalStep
    | false, visible => visible
    | true, visible => !visible
  nativeObserve _ := Prod.fst
  classicalObserve _ := _root_.id
  observeExact := by intros; rfl
  generatorExact := by
    intro generator native
    cases generator <;> cases native <;> rfl

theorem stableChartEveryWord (word : List Bool) (native : Bool × Bool) :
    stableChart.quotient (transportWord stableChart.nativeStep word native) =
      transportWord stableChart.classicalStep word (stableChart.quotient native) :=
  stableChart.everyOrderedWordExact word native

/-- A static first-coordinate face cannot descend through coordinate exchange. -/
theorem exchangeCannotDescendThroughFirstCoordinate :
    ¬ ∃ classicalStep : Bool → Bool,
      ∀ native : Bool × Bool,
        Prod.fst (Prod.swap native) = classicalStep (Prod.fst native) := by
  rintro ⟨classicalStep, exactStep⟩
  have left := exactStep (false, false)
  have right := exactStep (false, true)
  cases h : classicalStep false <;> simp [h] at left right

end Control

end Soma.Holonics.Computation.MachineLearningChart

section Audit
open Soma.Holonics.Computation.MachineLearningChart
#print axioms DynamicReceiverChart.everyOrderedWordExact
#print axioms quotientSuccessorTransformer_exists_iff
#print axioms DynamicReceiverChart.everyReceiverHistoryExact
#print axioms DynamicReceiverChart.quotientIsForwardSimulation
#print axioms DynamicReceiverChart.reconstructClassicalSuccessor
#print axioms DynamicReceiverChart.separatingHistoryReopensClassicalFace
#print axioms Control.stableChartEveryWord
#print axioms Control.exchangeCannotDescendThroughFirstCoordinate
end Audit
