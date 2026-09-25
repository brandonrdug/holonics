import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Defs

/-!
# Finite cross-entropy receiver

The generic finite cross-entropy chart and its action-indexed receiver fibre. Positivity and
normalization are carried as hypotheses on the receiver; the raw logarithmic expression remains
available independently of any membrane or physical interpretation.
-/

noncomputable section

open scoped BigOperators

namespace Holonics.Foundation.HolonicMembraneActionTransport

/-- Conventional finite cross-entropy. Positivity and normalization belong to a receiver chart;
this raw expression is kept separate so its exact quotient can be inspected. -/
def finiteCrossEntropy {Index : Type*} [Fintype Index]
    (reference emitted : Index → ℝ) : ℝ :=
  -∑ index, reference index * Real.log (emitted index)

/-- A probability receiver chart for one action population. The action itself remains arbitrary;
only its emitted receiver section is assigned normalized positive coordinates. -/
structure FiniteCrossEntropyReceiver (Action Index : Type*) [Fintype Index] where
  reference : Index → ℝ
  emitted : Action → Index → ℝ
  reference_nonnegative : ∀ index, 0 ≤ reference index
  reference_normalized : ∑ index, reference index = 1
  emitted_positive : ∀ action index, 0 < emitted action index
  emitted_normalized : ∀ action, ∑ index, emitted action index = 1

namespace FiniteCrossEntropyReceiver

variable {Action Index : Type*} [Fintype Index]

/-- The scalar face returned after the complete action has entered the probability chart. -/
def face (receiver : FiniteCrossEntropyReceiver Action Index) (action : Action) : ℝ :=
  finiteCrossEntropy receiver.reference (receiver.emitted action)

/-- The complete population of actions one scalar cross-entropy reading cannot distinguish. -/
def preimageFibre (receiver : FiniteCrossEntropyReceiver Action Index) (reading : ℝ) : Set Action :=
  {action | receiver.face action = reading}

@[simp] theorem mem_preimageFibre_iff
    (receiver : FiniteCrossEntropyReceiver Action Index) (reading : ℝ) (action : Action) :
    action ∈ receiver.preimageFibre reading ↔ receiver.face action = reading := Iff.rfl

/-- Equal cross-entropy puts two actions in one receiver fibre; it does not identify them. -/
theorem same_fibre_of_equal_face
    (receiver : FiniteCrossEntropyReceiver Action Index) {left right : Action}
    (equalFace : receiver.face left = receiver.face right) :
    left ∈ receiver.preimageFibre (receiver.face left) ∧
      right ∈ receiver.preimageFibre (receiver.face left) := by
  exact ⟨rfl, equalFace.symm⟩

/-- If a later receiver separates two equal-cross-entropy actions, that successor cannot factor
through the scalar cross-entropy face. -/
theorem no_successor_factor_of_equal_face
    {Successor : Type*}
    (receiver : FiniteCrossEntropyReceiver Action Index)
    (successor : Action → Successor) {left right : Action}
    (equalFace : receiver.face left = receiver.face right)
    (separated : successor left ≠ successor right) :
    ¬ ∃ factor : ℝ → Successor, ∀ action, successor action = factor (receiver.face action) := by
  intro witness
  apply separated
  exact Exists.elim witness fun factor factors =>
    calc
      successor left = factor (receiver.face left) := factors left
      _ = factor (receiver.face right) := congrArg factor equalFace
      _ = successor right := (factors right).symm

end FiniteCrossEntropyReceiver

end Holonics.Foundation.HolonicMembraneActionTransport

section Audit

#print axioms Holonics.Foundation.HolonicMembraneActionTransport.FiniteCrossEntropyReceiver.same_fibre_of_equal_face
#print axioms Holonics.Foundation.HolonicMembraneActionTransport.FiniteCrossEntropyReceiver.no_successor_factor_of_equal_face

end Audit
