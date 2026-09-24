import ElementaryHolonics.Computation.MachineLearningChart
import ElementaryHolonics.Computation.NativeMorphologyVariant

/-!
# Cultivation reopens a stale morphology projection

A `CultivationPassage` already owns the later-conduct witness, source-detached rest/remount,
chronology, withdrawal, and changed morphology required to distinguish learning from a fixed
inference cut.  This owner composes that complete passage with the standing
`ProjectedExportWitness`: any exterior projection which identifies the predecessor and successor
cannot remain exact at the passage's own witness probe.

No change flag or second lifecycle is introduced.  The unit receiver below is the honest
one-receiver presentation of `CultivationPassage.conduct`; it does not erase any receiver parameter
carried by that source owner.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicNeuralMorphologyContinuation

open Soma.Holonics.Computation.HolonicIntelligence
open Soma.Holonics.Computation.MachineLearningChart
open Soma.Holonics.Computation.NativeMorphologyVariant
open Soma.Holonics.Millennium.Chronology

/-- A cultivation passage and a projection which identifies its two morphologies return the
existing projected-export witness at the passage's own later-conduct separator. -/
def cultivationProjectedExportWitness
    {Morphology Difference Delta Probe Face RestIdentity Occurrence Export : Type*}
    (passage :
      CultivationPassage Morphology Difference Delta Probe Face RestIdentity Occurrence)
    (project : Morphology → Export)
    (collapsed : project passage.successor = project passage.predecessor) :
    ProjectedExportWitness Morphology Export Probe Unit Face where
  project := project
  nativeConduct := fun morphology probe _receiver ↦ passage.conduct morphology probe
  left := passage.successor
  right := passage.predecessor
  collapsed := collapsed
  separatingQuery := passage.witnessProbe
  separatingReceiver := ()
  separates := passage.changedLaterConduct

/-- Identifying predecessor and successor morphology is incompatible with exact conduct for every
later probe.  The contradiction is witnessed by the cultivation passage itself. -/
theorem cultivation_reopens_identifying_projection
    {Morphology Difference Delta Probe Face RestIdentity Occurrence Export : Type*}
    (passage :
      CultivationPassage Morphology Difference Delta Probe Face RestIdentity Occurrence)
    (project : Morphology → Export)
    (collapsed : project passage.successor = project passage.predecessor) :
    ¬ ∃ exportedConduct : Export → Probe → Unit → Face,
      ∀ morphology probe receiver,
        exportedConduct (project morphology) probe receiver =
          passage.conduct morphology probe :=
  (cultivationProjectedExportWitness passage project collapsed).richerReceiver_reopens_export

/-! ## Dynamic receiver charts across morphology change -/

/-- A predecessor chart transports to successor morphology only after the successor observation
and every successor generator return their exact commuting squares.  No chart label transports
these laws by itself. -/
def transportDynamicReceiverChartAcrossMorphology
    {Generator Receiver Native Classical Face : Type*}
    (predecessor : DynamicReceiverChart Generator Receiver Native Classical Face)
    (successorNativeStep : Generator → Native → Native)
    (successorNativeObserve : Receiver → Native → Face)
    (observeExact : ∀ receiver native,
      predecessor.classicalObserve receiver (predecessor.quotient native) =
        successorNativeObserve receiver native)
    (generatorExact : ∀ generator native,
      predecessor.quotient (successorNativeStep generator native) =
        predecessor.classicalStep generator (predecessor.quotient native)) :
    DynamicReceiverChart Generator Receiver Native Classical Face where
  quotient := predecessor.quotient
  nativeStep := successorNativeStep
  classicalStep := predecessor.classicalStep
  nativeObserve := successorNativeObserve
  classicalObserve := predecessor.classicalObserve
  observeExact := observeExact
  generatorExact := generatorExact

/-- Generator naturality on the cultivated morphology extends to every ordered successor word. -/
theorem transportedChart_everyOrderedWordExact
    {Generator Receiver Native Classical Face : Type*}
    (predecessor : DynamicReceiverChart Generator Receiver Native Classical Face)
    (successorNativeStep : Generator → Native → Native)
    (successorNativeObserve : Receiver → Native → Face)
    (observeExact : ∀ receiver native,
      predecessor.classicalObserve receiver (predecessor.quotient native) =
        successorNativeObserve receiver native)
    (generatorExact : ∀ generator native,
      predecessor.quotient (successorNativeStep generator native) =
        predecessor.classicalStep generator (predecessor.quotient native))
    (word : List Generator) (native : Native) :
    predecessor.quotient (transportWord successorNativeStep word native) =
      transportWord predecessor.classicalStep word (predecessor.quotient native) :=
  (transportDynamicReceiverChartAcrossMorphology predecessor successorNativeStep
    successorNativeObserve observeExact generatorExact).everyOrderedWordExact word native

/-- Exactness of one successor receiver after one ordered word.  This is deliberately stronger
than failure of a generator square: a square failure alone does not manufacture a receiver which
can observe it. -/
def SuccessorReceiverHistoryExact
    {Generator Receiver Native Classical Face : Type*}
    (predecessor : DynamicReceiverChart Generator Receiver Native Classical Face)
    (successorNativeStep : Generator → Native → Native)
    (successorNativeObserve : Receiver → Native → Face)
    (receiver : Receiver) (word : List Generator) (native : Native) : Prop :=
  predecessor.classicalObserve receiver
      (transportWord predecessor.classicalStep word (predecessor.quotient native)) =
    successorNativeObserve receiver (transportWord successorNativeStep word native)

/-- An actual observed obstruction at one word length. -/
def HasReceiverHistoryObstructionAtLength
    {Generator Receiver Native Classical Face : Type*}
    (predecessor : DynamicReceiverChart Generator Receiver Native Classical Face)
    (successorNativeStep : Generator → Native → Native)
    (successorNativeObserve : Receiver → Native → Face)
    (length : ℕ) : Prop :=
  ∃ receiver word native,
    word.length = length ∧
      ¬ SuccessorReceiverHistoryExact predecessor successorNativeStep
        successorNativeObserve receiver word native

/-- Any actual receiver-history failure has a shortest word.  The conclusion retains the receiver,
word, native occurrence, failure, and exactness of every strictly shorter receiver history. -/
theorem exists_shortest_receiverHistory_obstruction
    {Generator Receiver Native Classical Face : Type*}
    (predecessor : DynamicReceiverChart Generator Receiver Native Classical Face)
    (successorNativeStep : Generator → Native → Native)
    (successorNativeObserve : Receiver → Native → Face)
    (obstructed : ∃ receiver word native,
      ¬ SuccessorReceiverHistoryExact predecessor successorNativeStep
        successorNativeObserve receiver word native) :
    ∃ receiver word native,
      ¬ SuccessorReceiverHistoryExact predecessor successorNativeStep
        successorNativeObserve receiver word native ∧
      ∀ otherReceiver otherWord otherNative,
        otherWord.length < word.length →
          SuccessorReceiverHistoryExact predecessor successorNativeStep
            successorNativeObserve otherReceiver otherWord otherNative := by
  classical
  let P : ℕ → Prop := HasReceiverHistoryObstructionAtLength predecessor
    successorNativeStep successorNativeObserve
  have existsLength : ∃ length, P length := by
    obtain ⟨receiver, word, native, fails⟩ := obstructed
    exact ⟨word.length, receiver, word, native, rfl, fails⟩
  let least := Nat.find existsLength
  obtain ⟨receiver, word, native, wordLength, fails⟩ := Nat.find_spec existsLength
  refine ⟨receiver, word, native, fails, ?_⟩
  intro otherReceiver otherWord otherNative shorter
  by_contra otherFails
  have otherAtLength : P otherWord.length :=
    ⟨otherReceiver, otherWord, otherNative, rfl, otherFails⟩
  have leastLe := Nat.find_min' existsLength otherAtLength
  rw [wordLength] at shorter
  exact (not_lt_of_ge leastLe) shorter

namespace Control

/-- The constant exterior projection deliberately identifies the predecessor and successor of the
standing two-site cultivation passage. -/
def twoSiteConstantProjection : (Fin 2 → ℕ) → Unit := fun _ ↦ ()

/-- The standing changed probe at site zero reopens the constant projection. -/
theorem twoSiteConstantProjection_reopens :
    ¬ ∃ exportedConduct : Unit → Fin 2 → Unit → ℕ,
      ∀ morphology probe receiver,
        exportedConduct (twoSiteConstantProjection morphology) probe receiver =
          NativeMorphologyVariant.Control.twoSiteCultivationPassage.conduct morphology probe :=
  cultivation_reopens_identifying_projection
    NativeMorphologyVariant.Control.twoSiteCultivationPassage
    twoSiteConstantProjection rfl

/-- The unchanged stable chart is a positive transport control: successor observation and
generator squares are the standing exact squares. -/
def stableTransportedChart :
    DynamicReceiverChart Bool Unit (Bool × Bool) Bool Bool :=
  transportDynamicReceiverChartAcrossMorphology
    MachineLearningChart.Control.stableChart
    MachineLearningChart.Control.stableChart.nativeStep
    MachineLearningChart.Control.stableChart.nativeObserve
    MachineLearningChart.Control.stableChart.observeExact
    MachineLearningChart.Control.stableChart.generatorExact

theorem stableTransportedChart_everyWord (word : List Bool) (native : Bool × Bool) :
    stableTransportedChart.quotient
        (transportWord stableTransportedChart.nativeStep word native) =
      transportWord stableTransportedChart.classicalStep word
        (stableTransportedChart.quotient native) :=
  stableTransportedChart.everyOrderedWordExact word native

/-- The predecessor control keeps the visible coordinate fixed under its sole generator. -/
def swapPredecessorChart :
    DynamicReceiverChart Unit Unit (Bool × Bool) Bool Bool where
  quotient := Prod.fst
  nativeStep _ native := native
  classicalStep _ visible := visible
  nativeObserve _ := Prod.fst
  classicalObserve _ := id
  observeExact := by intros; rfl
  generatorExact := by intros; rfl

/-- Cultivated successor transport exchanges the previously visible and hidden coordinates. -/
def swapSuccessorNativeStep : Unit → (Bool × Bool) → (Bool × Bool) :=
  fun _ native ↦ native.swap

def swapSuccessorNativeObserve : Unit → (Bool × Bool) → Bool :=
  fun _ native ↦ native.1

/-- Present observation remains exact before any successor generator is applied. -/
theorem swap_emptyWord_exact (native : Bool × Bool) :
    SuccessorReceiverHistoryExact swapPredecessorChart swapSuccessorNativeStep
      swapSuccessorNativeObserve () [] native := by
  rfl

/-- One successor exchange separates the old chart at the explicit two-state occurrence. -/
theorem swap_oneStep_fails :
    ¬ SuccessorReceiverHistoryExact swapPredecessorChart swapSuccessorNativeStep
      swapSuccessorNativeObserve () [()] (false, true) := by
  intro exact
  change false = true at exact
  contradiction

/-- The swap reopening has an actual shortest observed obstruction, and its length is exactly one:
the empty word is exact while the singleton exchange fails. -/
theorem swap_shortest_obstruction_has_length_one :
    ∃ receiver word native,
      ¬ SuccessorReceiverHistoryExact swapPredecessorChart swapSuccessorNativeStep
        swapSuccessorNativeObserve receiver word native ∧
      word.length = 1 ∧
      ∀ otherReceiver otherWord otherNative,
        otherWord.length < word.length →
          SuccessorReceiverHistoryExact swapPredecessorChart swapSuccessorNativeStep
            swapSuccessorNativeObserve otherReceiver otherWord otherNative := by
  obtain ⟨receiver, word, native, fails, shortest⟩ :=
    exists_shortest_receiverHistory_obstruction swapPredecessorChart
      swapSuccessorNativeStep swapSuccessorNativeObserve
      ⟨(), [()], (false, true), swap_oneStep_fails⟩
  have lengthLe : word.length ≤ 1 := by
    by_contra notLe
    have oneLt : 1 < word.length := Nat.lt_of_not_ge notLe
    exact swap_oneStep_fails (shortest () [()] (false, true) oneLt)
  have lengthPos : 0 < word.length := by
    by_contra notPos
    have lengthZero : word.length = 0 := Nat.eq_zero_of_not_pos notPos
    have wordEmpty : word = [] := List.length_eq_zero_iff.mp lengthZero
    subst word
    exact fails (swap_emptyWord_exact native)
  have lengthOne : word.length = 1 := by omega
  exact ⟨receiver, word, native, fails, lengthOne, shortest⟩

end Control

section Audit

#print axioms cultivationProjectedExportWitness
#print axioms cultivation_reopens_identifying_projection
#print axioms transportedChart_everyOrderedWordExact
#print axioms exists_shortest_receiverHistory_obstruction
#print axioms Control.twoSiteConstantProjection_reopens
#print axioms Control.stableTransportedChart_everyWord
#print axioms Control.swap_emptyWord_exact
#print axioms Control.swap_oneStep_fails
#print axioms Control.swap_shortest_obstruction_has_length_one

end Audit

end Soma.Holonics.Computation.HolonicNeuralMorphologyContinuation
