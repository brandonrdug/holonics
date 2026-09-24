import Holonics.Foundation.Lineage

/-!
# Situated returned differences and their causal adjoint return

A returned difference belongs to its target fibre.  Rebasing it therefore requires two charts
and a commuting connection square; it is not a subtraction of ambient, context-free scalars.

Rebasing a returned difference requires two charts and a commuting connection square. The
general linearized adjoint along an addressed two-step word is owned by
`Transport/AddressedLinearizedPassage`; the results here retain the situated fibre comparison.
-/

noncomputable section

namespace Holonics.Millennium.SituatedReturnedDifference

universe uSource uTarget uSource' uTarget'

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

#print axioms dependentReturnedDifference_rebase

end Holonics.Millennium.SituatedReturnedDifference
