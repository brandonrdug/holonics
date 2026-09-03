import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ElementaryHolonics.Foundation.Lineage

/-!
# Situated returned differences and their causal adjoint return

A returned difference belongs to its target fibre.  Rebasing it therefore requires two charts
and a commuting connection square; it is not a subtraction of ambient, context-free scalars.

For a two-step addressed word, the linearized return travels in reverse order.  The occurrence
word is retained as an actual pullback join, while the radical and every preimage fibre are
carried by the same continuous-linear-map equality.  No inverse or injectivity hypothesis is used.
-/

noncomputable section

namespace Soma.Holonics.Millennium.SituatedReturnedDifference

universe uSource uTarget uSource' uTarget' uMiddle uOccurrence

section DependentDifference

variable {SourceFibre : Type uSource} {TargetFibre : Type uTarget}
variable {RebasedSourceFibre : Type uSource'} {RebasedTargetFibre : Type uTarget'}
variable [AddCommGroup SourceFibre] [AddCommGroup TargetFibre]
variable [AddCommGroup RebasedSourceFibre] [AddCommGroup RebasedTargetFibre]

/--
The exact connection square required to compare a returned difference before and after rebase.
The four carriers may be different fibres; no ambient scalar carrier is selected.
-/
structure DependentAdditiveConnectionSquare where
  /-- Transport from the situated source fibre into the situated target fibre. -/
  transport : SourceFibre ≃+ TargetFibre
  /-- The same connection expressed in the rebased source and target fibres. -/
  rebasedTransport : RebasedSourceFibre ≃+ RebasedTargetFibre
  /-- The chart on the source fibre. -/
  sourceChart : SourceFibre ≃+ RebasedSourceFibre
  /-- The chart on the target fibre. -/
  targetChart : TargetFibre ≃+ RebasedTargetFibre
  /-- Rebase commutes with connection transport at every situated source occurrence. -/
  connection_commutes :
    ∀ source, targetChart (transport source) = rebasedTransport (sourceChart source)

/-- The returned difference is formed in the target fibre after transporting the source. -/
def dependentReturnedDifference
    (transport : SourceFibre ≃+ TargetFibre)
    (source : SourceFibre) (target : TargetFibre) : TargetFibre :=
  target - transport source

/--
**Dependent returned-difference rebase.**  A commuting connection square transports the complete
target-fibre difference into the corresponding rebased target-fibre difference.
-/
theorem dependentReturnedDifference_rebase
    (square : DependentAdditiveConnectionSquare
      (SourceFibre := SourceFibre) (TargetFibre := TargetFibre)
      (RebasedSourceFibre := RebasedSourceFibre)
      (RebasedTargetFibre := RebasedTargetFibre))
    (source : SourceFibre) (target : TargetFibre) :
    square.targetChart (dependentReturnedDifference square.transport source target) =
      dependentReturnedDifference square.rebasedTransport
        (square.sourceChart source) (square.targetChart target) := by
  rw [dependentReturnedDifference, dependentReturnedDifference, map_sub,
    square.connection_commutes]

end DependentDifference

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

/--
**Reverse-order causal adjoint law.**  The adjoint of the two-step forward differential is the
successor adjoint followed by the predecessor adjoint, and construction requires the exact joined
occurrence word.
-/
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
  unfold addressedTwoStepAdjointPreimageFibre
    addressedTwoStepReversePreimageFibre
  rw [addressedTwoStep_adjoint_reverseOrder]

end AddressedAdjoint

#print axioms dependentReturnedDifference_rebase
#print axioms addressedTwoStep_adjoint_reverseOrder
#print axioms addressedTwoStep_adjointRadical_reverseOrder
#print axioms addressedTwoStep_adjointPreimageFibre_reverseOrder

end Soma.Holonics.Millennium.SituatedReturnedDifference
