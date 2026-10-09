import CMYAmbientSections
import CMYChartSheaf

/-! Recover the actual Y ambient CM square from the proved sections equation
and cached affine naturality. This avoids composing the large denominator
scheme equations. No action or chart-realization hypothesis is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yAmbientChartRing_square :
    yAmbientChartRingIso.hom ≫ yAmbientAppLE =
      CommRingCat.ofHom yDirectAwayIota ≫ yAmbientChartRingIso.hom := by
  change Proj.awayToSection CMGrading yCoordinate ≫ yAmbientAppLE =
    CommRingCat.ofHom yDirectAwayIota ≫ Proj.awayToSection CMGrading yCoordinate
  exact yAmbientSections_square

theorem yAmbientChartRing_inverse_square :
    yAmbientAppLE ≫ yAmbientChartRingIso.inv =
      yAmbientChartRingIso.inv ≫ CommRingCat.ofHom yDirectAwayIota := by
  apply (cancel_epi yAmbientChartRingIso.hom).mp
  rw [← Category.assoc, yAmbientChartRing_square, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

theorem yAmbient_fromSpec_action :
    yAmbientAffineOpen.2.fromSpec ≫ Proj.map gradedIota irrelevant_le_map_iota =
      Spec.map yAmbientAppLE ≫ yAmbientAffineOpen.2.fromSpec := by
  exact (IsAffineOpen.SpecMap_appLE_fromSpec
    (Proj.map gradedIota irrelevant_le_map_iota)
    yAmbientAffineOpen.2 yAmbientAffineOpen.2
    (show Proj.basicOpen CMGrading yCoordinate ≤
        (Proj.map gradedIota irrelevant_le_map_iota) ⁻¹ᵁ Proj.basicOpen CMGrading yCoordinate from
      Proj.basicOpen_mono CMGrading _ _ ⟨_, yCoordinate_actual_phase_inverse⟩)).symm

theorem yAwayIota_ambient_square :
    Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num) ≫
      projectiveAmbientIota.hom =
    Spec.map (CommRingCat.ofHom yAwayIota) ≫
      Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num) := by
  change Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num) ≫
    Proj.map gradedIota irrelevant_le_map_iota = _
  rw [← yDirectAwayIota_eq_existing, ← ySpecChart_fromSpec]
  rw [Category.assoc, yAmbient_fromSpec_action, ← Spec.map_comp_assoc,
    yAmbientChartRing_inverse_square, Spec.map_comp_assoc]

#print axioms yAmbientChartRing_square
#print axioms yAmbient_fromSpec_action
#print axioms yAwayIota_ambient_square
end Holonics.Hodge.CMGraphSource
