import CMZCubicChart

/-! The Z denominator is fixed, without importing the unrelated Y cubic proof. -/
noncomputable section
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra
@[simp] theorem zCoordinate_iota_fixed : gradedIota zCoordinate = zCoordinate := by
  simp [gradedIota, homogeneousIota, homogeneousPullback, zCoordinate]
#print axioms zCoordinate_iota_fixed
end Holonics.Hodge.CMGraphSource
