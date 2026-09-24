import Holonics.Foundation.Lineage
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linearized transport along addressed passages

A linearized passage retains both its differential and the addressed occurrences that carry it.
Serial differentials compose along an actual pullback join. Their adjoints compose in reverse
factor order, and the equality identifies both the receiver radical and every preimage fibre.
-/

noncomputable section

namespace Holonics.Transport

universe uSource uMiddle uTarget uOccurrence

section AddressedAdjoint

variable {Source : Type uSource} {Middle : Type uMiddle} {Target : Type uTarget}
variable [NormedAddCommGroup Source] [InnerProductSpace ℝ Source]
variable [FiniteDimensional ℝ Source]
variable [NormedAddCommGroup Middle] [InnerProductSpace ℝ Middle]
variable [FiniteDimensional ℝ Middle]
variable [NormedAddCommGroup Target] [InnerProductSpace ℝ Target]
variable [FiniteDimensional ℝ Target]

/-- An addressed passage together with its continuous linearized transport. -/
structure AddressedLinearizedPassage
    (Source : Type uSource) (Target : Type uTarget)
    [NormedAddCommGroup Source] [InnerProductSpace ℝ Source]
  [NormedAddCommGroup Target] [InnerProductSpace ℝ Target] where
  /-- The exact occurrence population and its two boundary maps. -/
  addressed : AddressedPassage.{uSource, uTarget, uOccurrence} Source Target
  /-- The local linearized transport carried by this passage. -/
  differential : Source →L[ℝ] Target

variable (first : AddressedLinearizedPassage Source Middle)
variable (second : AddressedLinearizedPassage Middle Target)

/-- The actual two-step word is a pullback join, not a pair of unconnected steps. -/
abbrev AddressedTwoStepWord := AddressedPassage.Join first.addressed second.addressed

/-- Forward linearized transport along one retained addressed two-step word. -/
def addressedTwoStepDifferential (_word : AddressedTwoStepWord first second) :
    Source →L[ℝ] Target :=
  second.differential.comp first.differential

/-- The causal adjoint return along that same word, in reverse transport order. -/
def addressedTwoStepReverseAdjoint (_word : AddressedTwoStepWord first second) :
    Target →L[ℝ] Source :=
  first.differential.adjoint.comp second.differential.adjoint

/-- The adjoint of the forward differential follows the joined word in reverse order. -/
theorem addressedTwoStep_adjoint_reverseOrder
    (word : AddressedTwoStepWord first second) :
    (addressedTwoStepDifferential first second word).adjoint =
      addressedTwoStepReverseAdjoint first second word := by
  exact ContinuousLinearMap.adjoint_comp second.differential first.differential

/-- The receiver-radical of the full adjoint composite. -/
def addressedTwoStepAdjointRadical (word : AddressedTwoStepWord first second) :
    Submodule ℝ Target :=
  (addressedTwoStepDifferential first second word).adjoint.ker

/-- The radical exhibited by the explicit reverse-order word. -/
def addressedTwoStepReverseRadical (word : AddressedTwoStepWord first second) :
    Submodule ℝ Target :=
  (addressedTwoStepReverseAdjoint first second word).ker

/-- The complete affine preimage fibre over a returned source-fibre value. -/
def addressedTwoStepAdjointPreimageFibre
    (word : AddressedTwoStepWord first second) (returned : Source) : Type uTarget :=
  { target : Target //
    (addressedTwoStepDifferential first second word).adjoint target = returned }

/-- The same preimage fibre read through the explicit reverse-order adjoint word. -/
def addressedTwoStepReversePreimageFibre
    (word : AddressedTwoStepWord first second) (returned : Source) : Type uTarget :=
  { target : Target //
    addressedTwoStepReverseAdjoint first second word target = returned }

/-- Reverse-order adjoint composition retains the exact radical. -/
theorem addressedTwoStep_adjointRadical_reverseOrder
    (word : AddressedTwoStepWord first second) :
    addressedTwoStepAdjointRadical first second word =
      addressedTwoStepReverseRadical first second word := by
  unfold addressedTwoStepAdjointRadical addressedTwoStepReverseRadical
  rw [addressedTwoStep_adjoint_reverseOrder]

/-- Reverse-order adjoint composition retains every complete preimage fibre. -/
theorem addressedTwoStep_adjointPreimageFibre_reverseOrder
    (word : AddressedTwoStepWord first second) (returned : Source) :
    addressedTwoStepAdjointPreimageFibre first second word returned =
      addressedTwoStepReversePreimageFibre first second word returned := by
  unfold addressedTwoStepAdjointPreimageFibre addressedTwoStepReversePreimageFibre
  rw [addressedTwoStep_adjoint_reverseOrder]

end AddressedAdjoint

#print axioms addressedTwoStep_adjoint_reverseOrder
#print axioms addressedTwoStep_adjointRadical_reverseOrder
#print axioms addressedTwoStep_adjointPreimageFibre_reverseOrder

end Holonics.Transport
