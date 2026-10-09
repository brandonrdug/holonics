import CMZChartAction
import CMChartStability

/-! Coordinate-map conjugacy under the proved actual reduced cubic Z chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zCubicChart_iota_conjugacy :
    zReducedCubicChartIso.inv ≫ cubicIotaZRestriction ≫ zReducedCubicChartIso.hom =
      Spec.map (CommRingCat.ofHom zIotaCoordinateRing) := by
  apply (cancel_mono (zReducedCubicChartIso.inv ≫ zCubicOpen.ι)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [cubicIotaZRestriction_ι]
  exact zCubicChart_iota_inclusion_square

#print axioms zCubicChart_iota_conjugacy
end Holonics.Hodge.CMGraphSource
