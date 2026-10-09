import CMZAmbientIdeals
import CMSpecKernelCoordinates
import CMZDiagonalLocal

/-! Coordinate descriptions of actual ambient ideal-sheaf restrictions,
using the existing Gamma-Spec isomorphism (not an assumed ideal identification). -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem zActualGraph_ideal_coordinates :
    cmConcreteComplexGraph.ker.comap zProductChartInclusion =
      Scheme.IdealSheafData.ofIdealTop
        (graphIdeal.map (Scheme.ΓSpecIso (.of ProductRing)).inv.hom) := by
  rw [zTensorGraph_actual_ideal]
  exact specMap_idealSheaf_coordinates (CommRingCat.ofHom graphReceiver.toRingHom)

theorem zActualDiagonal_ideal_coordinates :
    cmComplexDiagonal.ker.comap zProductChartInclusion =
      Scheme.IdealSheafData.ofIdealTop
        (diagonalIdeal.map (Scheme.ΓSpecIso (.of ProductRing)).inv.hom) := by
  rw [zTensorDiagonal_actual_ideal]
  exact specMap_idealSheaf_coordinates (CommRingCat.ofHom diagonalReceiver.toRingHom)

theorem zActualGraph_coordinates_restrict {U : Scheme} (r : U ⟶ Spec (.of ProductRing)) :
    cmConcreteComplexGraph.ker.comap (r ≫ zProductChartInclusion) =
      (Scheme.IdealSheafData.ofIdealTop
        (graphIdeal.map (Scheme.ΓSpecIso (.of ProductRing)).inv.hom)).comap r := by
  rw [Scheme.IdealSheafData.comap_comp, zActualGraph_ideal_coordinates]

theorem zActualDiagonal_coordinates_restrict {U : Scheme} (r : U ⟶ Spec (.of ProductRing)) :
    cmComplexDiagonal.ker.comap (r ≫ zProductChartInclusion) =
      (Scheme.IdealSheafData.ofIdealTop
        (diagonalIdeal.map (Scheme.ΓSpecIso (.of ProductRing)).inv.hom)).comap r := by
  rw [Scheme.IdealSheafData.comap_comp, zActualDiagonal_ideal_coordinates]

#print axioms zActualGraph_ideal_coordinates
#print axioms zActualDiagonal_ideal_coordinates
#print axioms zActualGraph_coordinates_restrict
#print axioms zActualDiagonal_coordinates_restrict
end Holonics.Hodge.CMGraphSource
