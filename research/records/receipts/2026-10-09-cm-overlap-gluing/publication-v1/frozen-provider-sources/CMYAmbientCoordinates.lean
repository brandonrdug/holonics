import CMYAmbientIdeals
import CMSpecKernelCoordinates
import CMYAmbientEquations

/-! Coordinate descriptions of actual ambient ideal-sheaf restrictions,
using the existing Gamma-Spec isomorphism (not an assumed ideal identification). -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem yActualGraph_ideal_coordinates :
    cmConcreteComplexGraph.ker.comap yProductChartInclusion =
      Scheme.IdealSheafData.ofIdealTop
        (yGraphIdeal.map (Scheme.ΓSpecIso (.of YProductRing)).inv.hom) := by
  rw [yTensorGraph_actual_ideal]
  exact specMap_idealSheaf_coordinates (CommRingCat.ofHom yGraphReceiver.toRingHom)

theorem yActualDiagonal_ideal_coordinates :
    cmComplexDiagonal.ker.comap yProductChartInclusion =
      Scheme.IdealSheafData.ofIdealTop
        (yDiagonalIdeal.map (Scheme.ΓSpecIso (.of YProductRing)).inv.hom) := by
  rw [yTensorDiagonal_actual_ideal]
  exact specMap_idealSheaf_coordinates (CommRingCat.ofHom yDiagonalReceiver.toRingHom)

theorem yActualGraph_coordinates_restrict {U : Scheme} (r : U ⟶ Spec (.of YProductRing)) :
    cmConcreteComplexGraph.ker.comap (r ≫ yProductChartInclusion) =
      (Scheme.IdealSheafData.ofIdealTop
        (yGraphIdeal.map (Scheme.ΓSpecIso (.of YProductRing)).inv.hom)).comap r := by
  rw [Scheme.IdealSheafData.comap_comp, yActualGraph_ideal_coordinates]

theorem yActualDiagonal_coordinates_restrict {U : Scheme} (r : U ⟶ Spec (.of YProductRing)) :
    cmComplexDiagonal.ker.comap (r ≫ yProductChartInclusion) =
      (Scheme.IdealSheafData.ofIdealTop
        (yDiagonalIdeal.map (Scheme.ΓSpecIso (.of YProductRing)).inv.hom)).comap r := by
  rw [Scheme.IdealSheafData.comap_comp, yActualDiagonal_ideal_coordinates]

#print axioms yActualGraph_ideal_coordinates
#print axioms yActualDiagonal_ideal_coordinates
#print axioms yActualGraph_coordinates_restrict
#print axioms yActualDiagonal_coordinates_restrict
end Holonics.Hodge.CMGraphSource
