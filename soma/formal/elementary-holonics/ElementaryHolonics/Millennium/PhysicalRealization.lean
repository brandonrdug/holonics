import ElementaryHolonics.Foundation.Lineage
import ElementaryHolonics.Foundation.Receiver
import ElementaryHolonics.Millennium.LineageCompression

/-!
# Physical realization passages retain lineage, future affect, fibres, and defects

`PhysicalRealizationCore` is the pure causal-algebraic face of a physical realization: its local
transport generators and declared receiver family.  The Rust realization receipt binds the
remaining situated occurrence, port, artifact and apparatus testimony.  Keeping that exterior
testimony out of this structure prevents a filesystem or device chart from becoming the
mathematics.

`RealizationSpan` carries an addressed occurrence population and a chart map.  It may have a local
generator defect.  `RealizationPassage` is the zero-defect case.  The defect of a composite span can
only come from the first span or from the second span at the transported intermediate state; for
linear charts the existing exact-matrix owner strengthens this union law to its additive chain law.

Occurrence identity, addressed-passage equivalence, receiver-history equivalence, rebase, and
compression are distinct types below.  Equal endpoints therefore never erase lineage, and a
non-injective compression returns its full reconstruction fibre rather than acquiring an inverse.

Every theorem is discharged and none depends on `sorryAx`.  This file proves no statement about a
named Millennium problem and does not claim that a supplied realization was recovered from
material.
-/

namespace Soma.Holonics.Millennium.PhysicalRealization

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology

universe uG uR uA uB uC uF uOcc

/-- The causal-algebraic core of one physical realization. -/
structure PhysicalRealizationCore
    (Generator : Type uG) (Receiver : Type uR) (State : Type uA) (Face : Type uF) where
  /-- The admitted local transport generators. -/
  transport : Generator → State → State
  /-- The declared receiver family. -/
  receiver : Receiver → State → Face

/-- One future receiver is a receiver together with an ordered transport word. -/
def futureFace
    {Generator : Type uG} {Receiver : Type uR} {State : Type uA} {Face : Type uF}
    (A : PhysicalRealizationCore Generator Receiver State Face)
    (receiver : Receiver) (word : List Generator) (state : State) : Face :=
  A.receiver receiver (transportWord A.transport word state)

/-- Equality under every admitted receiver and ordered successor history. -/
def ReceiverHistoryEquivalence
    {Generator : Type uG} {Receiver : Type uR} {State : Type uA} {Face : Type uF}
    (A : PhysicalRealizationCore Generator Receiver State Face) (left right : State) : Prop :=
  ∀ receiver word, futureFace A receiver word left = futureFace A receiver word right

/--
One entering apparatus receiver transformed into one later receiver/history face.

This is the exact mathematical position of a foreign model chart relative to a native consequence:
the entering face is construction testimony, while the returned face determines whether that
testimony is sufficient for this ordered future.
-/
abbrev ReceiverToFutureTransformer
    {Generator : Type uG} {Receiver : Type uR} {State : Type uA} {Face : Type uF}
    {EnteringFace : Type uB}
    (A : PhysicalRealizationCore Generator Receiver State Face)
    (entering : State → EnteringFace) (receiver : Receiver) (word : List Generator) :=
  ReceiverTransformer entering (futureFace A receiver word)

/--
The entering receiver descends to a later receiver/history exactly when its complete fibre is
invisible to that later receiver/history.
-/
theorem receiverToFutureTransformer_exists_iff
    {Generator : Type uG} {Receiver : Type uR} {State : Type uA} {Face : Type uF}
    {EnteringFace : Type uB}
    (A : PhysicalRealizationCore Generator Receiver State Face)
    (entering : State → EnteringFace) (receiver : Receiver) (word : List Generator) :
    Nonempty (ReceiverToFutureTransformer A entering receiver word) ↔
      ∀ left right, entering left = entering right →
        futureFace A receiver word left = futureFace A receiver word right :=
  receiverTransformer_exists_iff entering (futureFace A receiver word)

/-- Literal identity of two carrying occurrences. -/
def OccurrenceIdentity {Occurrence : Type*} (left right : Occurrence) : Prop := left = right

/-- Addressed passage equivalence preserves occurrence population and both boundary maps. -/
abbrev PassageEquivalence {X : Type uA} {Y : Type uB}
    (P Q : AddressedPassage.{uA, uB, uOcc} X Y) :=
  AddressedPassage.PassageEquiv P Q

/--
An addressed chart map before generator naturality has been required.

The addressed occurrence population is not derivable from `chart`: two spans may carry the same
map through different lineages.
-/
structure RealizationSpan
    {Generator : Type uG} {Receiver : Type uR} {Face : Type uF}
    {Source : Type uA} {Target : Type uB}
    (A : PhysicalRealizationCore Generator Receiver Source Face)
    (B : PhysicalRealizationCore Generator Receiver Target Face) where
  addressed : AddressedPassage.{uA, uB, uOcc} Source Target
  chart : Source → Target
  carries : ∀ source, Nonempty (addressed.Fibre source (chart source))
  receiverExact : ∀ receiver source, B.receiver receiver (chart source) = A.receiver receiver source

namespace RealizationSpan

variable {Generator : Type uG} {Receiver : Type uR} {Face : Type uF}
  {Source : Type uA} {Middle : Type uB} {Target : Type uC}
  {A : PhysicalRealizationCore Generator Receiver Source Face}
  {B : PhysicalRealizationCore Generator Receiver Middle Face}
  {C : PhysicalRealizationCore Generator Receiver Target Face}

/-- One local naturality defect. -/
def DefectAt (P : RealizationSpan A B) (generator : Generator) (source : Source) : Prop :=
  P.chart (A.transport generator source) ≠ B.transport generator (P.chart source)

/-- Serial composition retains the pullback occurrence population at the shared boundary. -/
noncomputable def comp (Q : RealizationSpan B C) (P : RealizationSpan A B) :
    RealizationSpan A C where
  addressed := AddressedPassage.comp Q.addressed P.addressed
  chart source := Q.chart (P.chart source)
  carries source := by
    rcases P.carries source with ⟨left⟩
    rcases Q.carries (P.chart source) with ⟨right⟩
    exact ⟨AddressedPassage.joinCompositeFibre Q.addressed P.addressed
      ⟨P.chart source, left, right⟩⟩
  receiverExact receiver source := by
    exact (Q.receiverExact receiver (P.chart source)).trans (P.receiverExact receiver source)

/--
The non-additive chain-defect law.

If the composite square fails at `source`, either the first square fails there or the second square
fails at the transported intermediate state.  Exact linear charts refine this union to
`χ_(η∘γ) = χ_η T_γ + S_η χ_γ`.
-/
theorem compositeDefectComesFromOneLocalPassage
    (Q : RealizationSpan B C) (P : RealizationSpan A B)
    (generator : Generator) (source : Source)
    (h : (Q.comp P).DefectAt generator source) :
    P.DefectAt generator source ∨ Q.DefectAt generator (P.chart source) := by
  by_cases firstDefect : P.DefectAt generator source
  · exact Or.inl firstDefect
  by_cases secondDefect : Q.DefectAt generator (P.chart source)
  · exact Or.inr secondDefect
  exfalso
  apply h
  have firstExact :
      P.chart (A.transport generator source) = B.transport generator (P.chart source) :=
    not_ne_iff.mp firstDefect
  have secondExact :
      Q.chart (B.transport generator (P.chart source)) =
        C.transport generator (Q.chart (P.chart source)) :=
    not_ne_iff.mp secondDefect
  exact calc
    Q.chart (P.chart (A.transport generator source)) =
        Q.chart (B.transport generator (P.chart source)) := congrArg Q.chart firstExact
    _ = C.transport generator (Q.chart (P.chart source)) := secondExact

end RealizationSpan

/-- A realization span whose chart commutes with every local generator. -/
structure RealizationPassage
    {Generator : Type uG} {Receiver : Type uR} {Face : Type uF}
    {Source : Type uA} {Target : Type uB}
    (A : PhysicalRealizationCore Generator Receiver Source Face)
    (B : PhysicalRealizationCore Generator Receiver Target Face) where
  span : RealizationSpan.{uG, uR, uA, uB, uF, uOcc} A B
  generatorExact : ∀ generator source,
    span.chart (A.transport generator source) = B.transport generator (span.chart source)

namespace RealizationPassage

variable {Generator : Type uG} {Receiver : Type uR} {Face : Type uF}
  {Source : Type uA} {Middle : Type uB} {Target : Type uC}
  {A : PhysicalRealizationCore Generator Receiver Source Face}
  {B : PhysicalRealizationCore Generator Receiver Middle Face}
  {C : PhysicalRealizationCore Generator Receiver Target Face}

/-- Local generator naturality extends to every ordered, possibly noncommuting word. -/
theorem chartCommutesWithEveryOrderedWord (P : RealizationPassage A B)
    (word : List Generator) (source : Source) :
    P.span.chart (transportWord A.transport word source) =
      transportWord B.transport word (P.span.chart source) :=
  generatorEquivarianceExtendsToEveryTransportWord
    A.transport B.transport P.span.chart P.generatorExact word source

/-- Every declared receiver and ordered successor history factors through the passage. -/
theorem everyFutureReceiverFactors (P : RealizationPassage A B)
    (receiver : Receiver) (word : List Generator) (source : Source) :
    futureFace B receiver word (P.span.chart source) = futureFace A receiver word source := by
  unfold futureFace
  rw [← P.chartCommutesWithEveryOrderedWord word source]
  exact P.span.receiverExact receiver (transportWord A.transport word source)

/-- Serially composing exact passages preserves addressed lineage and exact naturality. -/
noncomputable def comp (Q : RealizationPassage B C) (P : RealizationPassage A B) :
    RealizationPassage A C where
  span := Q.span.comp P.span
  generatorExact generator source := by
    exact calc
      Q.span.chart (P.span.chart (A.transport generator source)) =
          Q.span.chart (B.transport generator (P.span.chart source)) :=
        congrArg Q.span.chart (P.generatorExact generator source)
      _ = C.transport generator (Q.span.chart (P.span.chart source)) :=
        Q.generatorExact generator (P.span.chart source)

/-- The complete predecessor population behind one target face. -/
def reconstructionFibre (P : RealizationPassage A B) (target : Middle) : Type _ :=
  { source : Source // P.span.chart source = target }

/-- A proposed affect class is reopened by one receiver and ordered history. -/
structure SeparatingReceiverHistory (P : RealizationPassage A B) (left right : Source) where
  receiver : Receiver
  word : List Generator
  separates : futureFace A receiver word left ≠ futureFace A receiver word right

/-- A rebase owes a passage back and both literal identity compositions. -/
structure Rebase (P : RealizationPassage A B) where
  inverse : RealizationPassage.{uG, uR, uB, uA, uF, uOcc} B A
  forwardIdentity : ∀ source, inverse.span.chart (P.span.chart source) = source
  backwardIdentity : ∀ target, P.span.chart (inverse.span.chart target) = target

/-- A non-injective realization passage is compression, with the collapsed fibre exhibited. -/
structure Compression (P : RealizationPassage A B) where
  left : Source
  right : Source
  distinct : left ≠ right
  sameTarget : P.span.chart left = P.span.chart right

/-- A compression witness places both distinct sources in one complete reconstruction fibre. -/
def Compression.bothInOneFibre (P : RealizationPassage A B) (K : P.Compression) :
    P.reconstructionFibre (P.span.chart K.left) ×
      P.reconstructionFibre (P.span.chart K.left) :=
  (⟨K.left, rfl⟩, ⟨K.right, K.sameTarget.symm⟩)

end RealizationPassage

/-! ## Controls: equal endpoints are not lineage, and static equality can reopen -/

def unitRealization : PhysicalRealizationCore Unit Unit Unit Unit where
  transport _ := _root_.id
  receiver _ := _root_.id

def singleUnitRealizationPassage : RealizationPassage unitRealization unitRealization where
  span :=
    { addressed := AddressedPassage.singleUnitPassage
      chart := _root_.id
      carries := fun _ ↦ ⟨⟨(), rfl, rfl⟩⟩
      receiverExact := fun _ _ ↦ rfl }
  generatorExact _ _ := rfl

def parallelUnitRealizationPassage : RealizationPassage unitRealization unitRealization where
  span :=
    { addressed := AddressedPassage.parallelUnitPassage
      chart := _root_.id
      carries := fun _ ↦ ⟨⟨false, rfl, rfl⟩⟩
      receiverExact := fun _ _ ↦ rfl }
  generatorExact _ _ := rfl

/-- The two passages have the same endpoint map. -/
theorem theSameEndpointMapCanCarryDifferentLineage :
    singleUnitRealizationPassage.span.chart = parallelUnitRealizationPassage.span.chart := rfl

/-- Equal endpoint maps do not produce an addressed passage equivalence. -/
theorem equalEndpointsDoNotIdentifyPassages :
    PassageEquivalence singleUnitRealizationPassage.span.addressed
      parallelUnitRealizationPassage.span.addressed → False := by
  intro equivalent
  obtain ⟨left, left_image⟩ := equivalent.occurrence.surjective false
  obtain ⟨right, right_image⟩ := equivalent.occurrence.surjective true
  have same_source : left = right := by
    change (left : Unit) = right
    cases left
    cases right
    rfl
  rw [same_source] at left_image
  exact Bool.false_ne_true (left_image.symm.trans right_image)

open Soma.Holonics.Millennium.LineageCompression.ReceiverHistoryCompression.StaticControl

def staticSourceRealization :
    PhysicalRealizationCore Unit Unit (Bool × Bool) Bool where
  transport _ := exchangeCoordinates
  receiver _ := Prod.fst

def staticTargetRealization : PhysicalRealizationCore Unit Unit Bool Bool where
  transport _ := _root_.id
  receiver _ := _root_.id

/--
The present-exact first-coordinate map cannot become a realization passage: one successor exposes
the second coordinate and breaks its generator square.
-/
theorem staticEqualityCannotPoseAsSuccessorExact
    (P : RealizationPassage staticSourceRealization staticTargetRealization)
    (chartIsFirst : P.span.chart = Prod.fst) : False := by
  have exact := P.generatorExact () (false, true)
  simp only [staticSourceRealization, staticTargetRealization, exchangeCoordinates] at exact
  rw [chartIsFirst] at exact
  simp at exact

end Soma.Holonics.Millennium.PhysicalRealization

section Audit
open Soma.Holonics.Millennium.PhysicalRealization
#print axioms RealizationSpan.compositeDefectComesFromOneLocalPassage
#print axioms RealizationPassage.chartCommutesWithEveryOrderedWord
#print axioms RealizationPassage.everyFutureReceiverFactors
#print axioms RealizationPassage.comp
#print axioms equalEndpointsDoNotIdentifyPassages
#print axioms staticEqualityCannotPoseAsSuccessorExact
end Audit
