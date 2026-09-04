import ElementaryHolonics.Foundation.AddressedBoundary
import ElementaryHolonics.Millennium.PhysicalRealization

/-!
# Dependent receiver histories on one connected addressed realization

This module supplies the generic carrier needed when different receivers return genuinely
different face types.  One state population carries one generator action.  Its complete causal
signature is the dependent family of faces returned after every ordered generator word.

Serial realization passages are connected only by the actual pullback population of
`AddressedPassage.Join`.  Equal occurrence counts, independently inhabited components, or equal
relational shadows are not a substitute for the joining equality.

Every theorem is discharged.  The finite controls at the end use two one-occurrence passages:
the disconnected pair has the same component populations but no join, while the exactly matched
pair inhabits the composite fibre.
-/

namespace Soma.Holonics.Millennium.DependentConnectedRealization

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology

universe uG uR uS uQ uF uA uB uC uOcc

/-! ## One state/action with a dependent receiver family -/

/-- One state population and generator action observed through a genuinely dependent receiver
family.  A receiver chooses its own face type. -/
structure DependentRealizationCore
    (Generator : Type uG) (Receiver : Type uR) (State : Type uS)
    (Face : Receiver → Type uF) where
  transport : Generator → State → State
  receiver : (receiver : Receiver) → State → Face receiver

/-- The face returned by one receiver after one ordered, possibly noncommuting, transport word. -/
def futureFace
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    (A : DependentRealizationCore Generator Receiver State Face)
    (receiver : Receiver) (word : List Generator) (state : State) : Face receiver :=
  A.receiver receiver (transportWord A.transport word state)

/-- The complete dependent receiver/history signature of one state. -/
def causalSignature
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    (A : DependentRealizationCore Generator Receiver State Face) (state : State) :
    (receiver : Receiver) → List Generator → Face receiver :=
  fun receiver word => futureFace A receiver word state

/-! ## Complete dependent receiver-history quotient -/

/-- A generator-equivariant quotient which is sound and complete for the entire dependent
receiver/history signature. -/
structure CompleteDependentReceiverHistoryQuotient
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    (A : DependentRealizationCore Generator Receiver State Face) (Quotient : Type uQ) where
  quotient : State → Quotient
  quotientTransport : Generator → Quotient → Quotient
  generatorExact : ∀ generator state,
    quotient (A.transport generator state) =
      quotientTransport generator (quotient state)
  sound : ∀ {left right : State}, quotient left = quotient right →
    causalSignature A left = causalSignature A right
  complete : ∀ {left right : State},
    causalSignature A left = causalSignature A right → quotient left = quotient right

namespace CompleteDependentReceiverHistoryQuotient

variable {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
  {Face : Receiver → Type uF}
  {A : DependentRealizationCore Generator Receiver State Face} {Quotient : Type uQ}
  (C : CompleteDependentReceiverHistoryQuotient A Quotient)

/-- Generator descent extends to every ordered word without flattening chronology. -/
theorem quotientCommutesWithEveryOrderedWord (word : List Generator) (state : State) :
    C.quotient (transportWord A.transport word state) =
      transportWord C.quotientTransport word (C.quotient state) :=
  generatorEquivarianceExtendsToEveryTransportWord
    A.transport C.quotientTransport C.quotient C.generatorExact word state

/-- Quotient equality is exactly equality of the complete dependent causal signature. -/
theorem quotientEq_iff_causalSignatureEq {left right : State} :
    C.quotient left = C.quotient right ↔
      causalSignature A left = causalSignature A right :=
  ⟨C.sound, C.complete⟩

/-- Unequal quotient states return a receiver and ordered word which separate them. -/
theorem quotientNe_returnsSeparatingReceiverHistory {left right : State}
    (different : C.quotient left ≠ C.quotient right) :
    ∃ receiver word,
      futureFace A receiver word left ≠ futureFace A receiver word right := by
  classical
  by_contra noSeparator
  apply different
  apply C.complete
  apply funext
  intro receiver
  apply funext
  intro word
  by_contra separated
  exact noSeparator ⟨receiver, word, separated⟩

/-- The complete source population behind one quotient state. -/
def preimageFibre (quotient : Quotient) : Type uS :=
  { state : State // C.quotient state = quotient }

end CompleteDependentReceiverHistoryQuotient

/-! ## Exact dependent factorization or exact insufficiency -/

/-- A single entering face factors every dependent receiver after every ordered history. -/
structure DependentReceiverHistoryTransformer
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    (A : DependentRealizationCore Generator Receiver State Face)
    {Entering : Type uA} (entering : State → Entering) where
  transform : (receiver : Receiver) → List Generator → Set.range entering → Face receiver
  exact : ∀ receiver word state,
    transform receiver word ⟨entering state, ⟨state, rfl⟩⟩ =
      futureFace A receiver word state

namespace DependentReceiverHistoryTransformer

variable {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
  {Face : Receiver → Type uF}
  {A : DependentRealizationCore Generator Receiver State Face}
  {Entering : Type uA} {entering : State → Entering}

/-- Restricting a dependent history transformer to one receiver and word returns the existing exact
`ReceiverTransformer` carrier. -/
def atReceiverHistory (transformer : DependentReceiverHistoryTransformer A entering)
    (receiver : Receiver) (word : List Generator) :
    ReceiverTransformer entering (futureFace A receiver word) where
  transform := transformer.transform receiver word
  exact := transformer.exact receiver word

end DependentReceiverHistoryTransformer

/-- The dependent history family factors exactly through the entering face precisely when every
receiver/history is constant on each complete entering fibre. -/
theorem dependentReceiverHistoryTransformer_exists_iff
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    (A : DependentRealizationCore Generator Receiver State Face)
    {Entering : Type uA} (entering : State → Entering) :
    Nonempty (DependentReceiverHistoryTransformer A entering) ↔
      ∀ receiver word left right, entering left = entering right →
        futureFace A receiver word left = futureFace A receiver word right := by
  constructor
  · rintro ⟨transformer⟩ receiver word left right sameEntering
    exact (receiverTransformer_exists_iff entering (futureFace A receiver word)).mp
      ⟨transformer.atReceiverHistory receiver word⟩ left right sameEntering
  · intro identified
    classical
    refine ⟨{
      transform := fun receiver word face =>
        futureFace A receiver word (Classical.choose face.property)
      exact := ?_
    }⟩
    intro receiver word state
    exact identified receiver word _ state
      (Classical.choose_spec
        (show entering state ∈ Set.range entering from ⟨state, rfl⟩))

/-- An exact dependent insufficiency retains the receiver, ordered word, and the existing
`ReceiverInsufficiency` witness inside one entering fibre. -/
structure DependentReceiverHistoryInsufficiency
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    (A : DependentRealizationCore Generator Receiver State Face)
    {Entering : Type uA} (entering : State → Entering) where
  receiver : Receiver
  word : List Generator
  witness : ReceiverInsufficiency entering (futureFace A receiver word)

/-- Every dependent receiver/history family returns either an exact factorization or a concrete
`ReceiverInsufficiency`.  No representative is selected from an unresolved entering fibre. -/
theorem exactFactorizationOrReceiverInsufficiency
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    (A : DependentRealizationCore Generator Receiver State Face)
    {Entering : Type uA} (entering : State → Entering) :
    Nonempty (DependentReceiverHistoryTransformer A entering) ∨
      Nonempty (DependentReceiverHistoryInsufficiency A entering) := by
  classical
  by_cases factors : ∀ receiver word left right, entering left = entering right →
      futureFace A receiver word left = futureFace A receiver word right
  · exact Or.inl ((dependentReceiverHistoryTransformer_exists_iff A entering).mpr factors)
  · push_neg at factors
    obtain ⟨receiver, word, left, right, sameEntering, differentReturned⟩ := factors
    exact Or.inr ⟨{
      receiver := receiver
      word := word
      witness := {
        left := left
        right := right
        sameEntering := sameEntering
        differentReturned := differentReturned
      }
    }⟩

/-- Exact dependent factorization and a receiver insufficiency cannot coexist. -/
theorem DependentReceiverHistoryTransformer.excludesInsufficiency
    {Generator : Type uG} {Receiver : Type uR} {State : Type uS}
    {Face : Receiver → Type uF}
    {A : DependentRealizationCore Generator Receiver State Face}
    {Entering : Type uA} {entering : State → Entering}
    (transformer : DependentReceiverHistoryTransformer A entering)
    (insufficiency : DependentReceiverHistoryInsufficiency A entering) : False := by
  let leftFace : Set.range entering :=
    ⟨entering insufficiency.witness.left, ⟨insufficiency.witness.left, rfl⟩⟩
  let rightFace : Set.range entering :=
    ⟨entering insufficiency.witness.right, ⟨insufficiency.witness.right, rfl⟩⟩
  have sameFace : leftFace = rightFace := Subtype.ext insufficiency.witness.sameEntering
  apply insufficiency.witness.differentReturned
  exact calc
    futureFace A insufficiency.receiver insufficiency.word insufficiency.witness.left =
        transformer.transform insufficiency.receiver insufficiency.word leftFace :=
      (transformer.exact _ _ _).symm
    _ = transformer.transform insufficiency.receiver insufficiency.word rightFace :=
      congrArg (transformer.transform insufficiency.receiver insufficiency.word) sameFace
    _ = futureFace A insufficiency.receiver insufficiency.word insufficiency.witness.right :=
      transformer.exact _ _ _

/-! ## Connected addressed realization passages -/

/-- A dependent realization passage carries every source through an addressed occurrence, preserves
every dependent receiver, and commutes with every local generator. -/
structure AddressedDependentRealizationPassage
    {Generator : Type uG} {Receiver : Type uR} {Face : Receiver → Type uF}
    {Source : Type uA} {Target : Type uB}
    (A : DependentRealizationCore Generator Receiver Source Face)
    (B : DependentRealizationCore Generator Receiver Target Face) where
  addressed : AddressedPassage.{uA, uB, uOcc} Source Target
  chart : Source → Target
  carries : ∀ source, Nonempty (addressed.Fibre source (chart source))
  receiverExact : ∀ receiver source,
    B.receiver receiver (chart source) = A.receiver receiver source
  generatorExact : ∀ generator source,
    chart (A.transport generator source) = B.transport generator (chart source)

namespace AddressedDependentRealizationPassage

variable {Generator : Type uG} {Receiver : Type uR} {Face : Receiver → Type uF}
  {Source : Type uA} {Middle : Type uB} {Target : Type uC}
  {A : DependentRealizationCore Generator Receiver Source Face}
  {B : DependentRealizationCore Generator Receiver Middle Face}
  {C : DependentRealizationCore Generator Receiver Target Face}

/-- Serial composition uses the addressed pullback occurrence population and retains its joining
equality; it does not infer connection from the component populations. -/
noncomputable def comp (Q : AddressedDependentRealizationPassage B C)
    (P : AddressedDependentRealizationPassage A B) :
    AddressedDependentRealizationPassage A C where
  addressed := AddressedPassage.comp Q.addressed P.addressed
  chart source := Q.chart (P.chart source)
  carries source := by
    rcases P.carries source with ⟨left⟩
    rcases Q.carries (P.chart source) with ⟨right⟩
    exact ⟨AddressedPassage.joinCompositeFibre Q.addressed P.addressed
      ⟨P.chart source, left, right⟩⟩
  receiverExact receiver source :=
    (Q.receiverExact receiver (P.chart source)).trans (P.receiverExact receiver source)
  generatorExact generator source := by
    rw [P.generatorExact, Q.generatorExact]

/-- Generator exactness extends to the complete ordered chronology. -/
theorem chartCommutesWithEveryOrderedWord
    (P : AddressedDependentRealizationPassage A B)
    (word : List Generator) (source : Source) :
    P.chart (transportWord A.transport word source) =
      transportWord B.transport word (P.chart source) :=
  generatorEquivarianceExtendsToEveryTransportWord
    A.transport B.transport P.chart P.generatorExact word source

/-- Every dependent receiver after every ordered successor history factors through the passage. -/
theorem everyFutureReceiverFactors
    (P : AddressedDependentRealizationPassage A B)
    (receiver : Receiver) (word : List Generator) (source : Source) :
    futureFace B receiver word (P.chart source) = futureFace A receiver word source := by
  unfold futureFace
  rw [← P.chartCommutesWithEveryOrderedWord word source]
  exact P.receiverExact receiver (transportWord A.transport word source)

end AddressedDependentRealizationPassage

/-- Exact connectedness from `source` to `target` through two adjacent passages means that the
composite addressed fibre is inhabited.  Its inhabitant contains both occurrences and their exact
middle-boundary equality. -/
def PullbackConnectedAt
    {X : Type uA} {Y : Type uB} {Z : Type uC}
    (P : AddressedPassage.{uA, uB, uOcc} X Y)
    (Q : AddressedPassage.{uB, uC, uOcc} Y Z) (source : X) (target : Z) : Prop :=
  Nonempty ((AddressedPassage.comp Q P).Fibre source target)

/-- The connectedness criterion is exactly an addressed joined occurrence with both exterior
boundary equalities; no cardinality premise appears. -/
theorem pullbackConnectedAt_iff_exists_join
    {X : Type uA} {Y : Type uB} {Z : Type uC}
    (P : AddressedPassage.{uA, uB, uOcc} X Y)
    (Q : AddressedPassage.{uB, uC, uOcc} Y Z) (source : X) (target : Z) :
    PullbackConnectedAt P Q source target ↔
      ∃ joined : AddressedPassage.Join P Q,
        P.source joined.left = source ∧ Q.target joined.right = target := by
  constructor
  · rintro ⟨⟨joined, sourceExact, targetExact⟩⟩
    exact ⟨joined, sourceExact, targetExact⟩
  · rintro ⟨joined, sourceExact, targetExact⟩
    exact ⟨⟨joined, sourceExact, targetExact⟩⟩

/-- A connected composite returns exact cancellation of its joined middle boundary. -/
theorem pullbackConnected_returnsMiddleBoundaryCancellation
    {X : Type uA} {Y : Type uB} {Z : Type uC}
    (P : AddressedPassage.{uA, uB, uOcc} X Y)
    (Q : AddressedPassage.{uB, uC, uOcc} Y Z) (source : X) (target : Z)
    (connected : PullbackConnectedAt P Q source target) :
    ∃ joined : AddressedPassage.Join P Q,
      P.source joined.left = source ∧ Q.target joined.right = target ∧
        P.joinedMiddleBoundary Q joined = 0 := by
  rcases connected with ⟨⟨joined, sourceExact, targetExact⟩⟩
  exact ⟨joined, sourceExact, targetExact, AddressedPassage.boundary_join P Q joined⟩

/-- Composable dependent realization passages are connected at every chart-carried source by an
actual pullback occurrence. -/
theorem realizationPassagesArePullbackConnected
    {Generator : Type uG} {Receiver : Type uR} {Face : Receiver → Type uF}
    {Source : Type uA} {Middle : Type uB} {Target : Type uC}
    {A : DependentRealizationCore Generator Receiver Source Face}
    {B : DependentRealizationCore Generator Receiver Middle Face}
    {C : DependentRealizationCore Generator Receiver Target Face}
    (P : AddressedDependentRealizationPassage A B)
    (Q : AddressedDependentRealizationPassage B C) (source : Source) :
    PullbackConnectedAt P.addressed Q.addressed source (Q.chart (P.chart source)) :=
  (Q.comp P).carries source

/-! ## Executable finite controls -/

namespace FiniteControls

inductive MiddleBoundary where
  | left
  | right
  deriving DecidableEq

/-- One predecessor occurrence ending at the left middle boundary. -/
def predecessor : AddressedPassage Unit MiddleBoundary where
  Occurrence := Unit
  source _ := ()
  target _ := .left

/-- One independently inhabited successor occurrence beginning at the other middle boundary. -/
def disconnectedSuccessor : AddressedPassage MiddleBoundary Unit where
  Occurrence := Unit
  source _ := .right
  target _ := ()

/-- The same one-occurrence successor population, now beginning at the exact shared boundary. -/
def connectedSuccessor : AddressedPassage MiddleBoundary Unit where
  Occurrence := Unit
  source _ := .left
  target _ := ()

/-- Executable boundary test for the two one-occurrence controls. -/
def admitsTheUniqueJoin (successor : AddressedPassage MiddleBoundary Unit)
    (occurrence : successor.Occurrence) : Bool :=
  decide (predecessor.target () = successor.source occurrence)

/-- The disconnected tuple has two inhabited one-occurrence components but the executable
pullback test refuses their unequal middle boundaries. -/
theorem disconnectedTupleIsRefused :
    admitsTheUniqueJoin disconnectedSuccessor () = false := by
  decide

/-- The exactly matched pair passes the executable pullback test. -/
theorem exactPullbackIsAdmitted :
    admitsTheUniqueJoin connectedSuccessor () = true := by
  decide

/-- The refusal is structural: the disconnected pair has no `Join` inhabitant. -/
theorem disconnectedTupleHasNoJoin :
    IsEmpty (AddressedPassage.Join predecessor disconnectedSuccessor) := by
  constructor
  intro joined
  cases joined.joins

/-- The admitted control contains the actual pullback witness. -/
def exactPullbackJoin : AddressedPassage.Join predecessor connectedSuccessor where
  left := ()
  right := ()
  joins := rfl

/-- The exact pullback witness inhabits the complete composite fibre. -/
theorem exactPullbackConnected :
    PullbackConnectedAt predecessor connectedSuccessor () () :=
  ⟨⟨exactPullbackJoin, rfl, rfl⟩⟩

/-- Consequently the equal-sized but disconnected tuple fails the connectedness criterion. -/
theorem disconnectedTupleNotConnected :
    ¬ PullbackConnectedAt predecessor disconnectedSuccessor () () := by
  rintro ⟨carried⟩
  exact disconnectedTupleHasNoJoin.false carried.1

end FiniteControls

end Soma.Holonics.Millennium.DependentConnectedRealization

section Audit
open Soma.Holonics.Millennium.DependentConnectedRealization
#print axioms CompleteDependentReceiverHistoryQuotient.quotientCommutesWithEveryOrderedWord
#print axioms CompleteDependentReceiverHistoryQuotient.quotientEq_iff_causalSignatureEq
#print axioms CompleteDependentReceiverHistoryQuotient.quotientNe_returnsSeparatingReceiverHistory
#print axioms dependentReceiverHistoryTransformer_exists_iff
#print axioms exactFactorizationOrReceiverInsufficiency
#print axioms DependentReceiverHistoryTransformer.excludesInsufficiency
#print axioms AddressedDependentRealizationPassage.everyFutureReceiverFactors
#print axioms pullbackConnectedAt_iff_exists_join
#print axioms pullbackConnected_returnsMiddleBoundaryCancellation
#print axioms realizationPassagesArePullbackConnected
#print axioms FiniteControls.disconnectedTupleIsRefused
#print axioms FiniteControls.exactPullbackIsAdmitted
#print axioms FiniteControls.disconnectedTupleHasNoJoin
#print axioms FiniteControls.exactPullbackConnected
#print axioms FiniteControls.disconnectedTupleNotConnected
end Audit
