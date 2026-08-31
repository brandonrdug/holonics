import ElementaryHolonics.Computation.SituatedMachineLearning

/-!
# Dependent holonic carriers and fixed-state machine charts

Changing incidence or available local carrier does not escape mathematics: the complete dependent
population can always be totalized as a sigma type, which is itself one fixed state type.  The
strict gain is therefore relative to a declared compressed classical chart.  Such a chart fails
exactly when two total states it identifies are separated by an admitted reconfiguration.
-/

namespace Soma.Holonics.Computation.DependentMachineLearningCarrier

open Soma.Holonics.Computation.MachineLearningChart

universe uG uS uC uR

/-- A generator may change both the carrier shape and the state living over that shape. -/
structure DependentTransport
    (Generator : Type uG) (Shape : Type uS) (Carrier : Shape → Type uC) where
  nextShape : Generator → Shape → Shape
  conduct : ∀ generator shape, Carrier shape → Carrier (nextShape generator shape)

namespace DependentTransport

variable {Generator : Type uG} {Shape : Type uS} {Carrier : Shape → Type uC}
  (D : DependentTransport Generator Shape Carrier)

/-- The exact total state retains its current shape together with the state in that fibre. -/
abbrev TotalState (Carrier : Shape → Type uC) := Σ shape, Carrier shape

/-- One dependent transport is a total transport on the exact sigma carrier. -/
def totalStep (generator : Generator) : TotalState Carrier → TotalState Carrier
  | ⟨shape, state⟩ => ⟨D.nextShape generator shape, D.conduct generator shape state⟩

/-- The sigma totalization is an exact fixed-state chart; no expressivity claim is obtained for free. -/
def exactTotalizationChart :
    DynamicReceiverChart Generator Unit (TotalState Carrier)
      (TotalState Carrier) (TotalState Carrier) where
  quotient := _root_.id
  nativeStep := totalStep D
  classicalStep := totalStep D
  nativeObserve _ := _root_.id
  classicalObserve _ := _root_.id
  observeExact := by intros; rfl
  generatorExact := by intros; rfl

/-- Every dependent transport word therefore has an exact fixed sigma-type presentation. -/
theorem totalizationEveryWordExact (word : List Generator) (state : TotalState Carrier) :
    (exactTotalizationChart D).quotient
        (Soma.Holonics.Millennium.Chronology.transportWord (totalStep D) word state) =
      Soma.Holonics.Millennium.Chronology.transportWord (totalStep D) word
        ((exactTotalizationChart D).quotient state) :=
  (exactTotalizationChart D).everyOrderedWordExact word state

/-- A proposed compressed fixed state descends only if every dependent generator commutes. -/
def DescendsTo
    (Classical : Type uR) (quotient : TotalState Carrier → Classical)
    (classicalStep : Generator → Classical → Classical) : Prop :=
  ∀ generator state,
    quotient (totalStep D generator state) = classicalStep generator (quotient state)

/--
One reconfiguration which exposes a distinction collapsed by the fixed chart obstructs every
classical transition family on that chart.
-/
theorem separatedReconfiguration_obstructsEveryFixedDescent
    {Classical : Type uR} (quotient : TotalState Carrier → Classical)
    (generator : Generator) (left right : TotalState Carrier)
    (samePresent : quotient left = quotient right)
    (differentFuture :
      quotient (totalStep D generator left) ≠ quotient (totalStep D generator right)) :
    ¬ ∃ classicalStep : Generator → Classical → Classical,
      DescendsTo D Classical quotient classicalStep := by
  rintro ⟨classicalStep, descends⟩
  apply differentFuture
  rw [descends, descends, samePresent]

/-- The complete dependent reconstruction fibre behind one fixed classical face. -/
def reconstructionFibre
    {Classical : Type uR} (quotient : TotalState Carrier → Classical) (face : Classical) :
    Type (max uS uC) :=
  { state : TotalState Carrier // quotient state = face }

end DependentTransport

end Soma.Holonics.Computation.DependentMachineLearningCarrier

section Audit
open Soma.Holonics.Computation.DependentMachineLearningCarrier
#print axioms DependentTransport.totalizationEveryWordExact
#print axioms DependentTransport.separatedReconfiguration_obstructsEveryFixedDescent
end Audit
