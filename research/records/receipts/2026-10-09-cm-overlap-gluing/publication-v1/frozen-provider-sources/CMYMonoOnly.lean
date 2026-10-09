import CMYChartAction

/-! Isolate the actual chart inclusion's monomorphism evidence without creating
a new definition of its (large, reducible) scheme-valued composite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yActualChartInclusion_mono :
    Mono (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) := by
  infer_instance

#print axioms yActualChartInclusion_mono
end Holonics.Hodge.CMGraphSource
