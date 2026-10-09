import CMYQuotientMap

/-! The proved Y chart isomorphism has its actual ambient inclusion square. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yCubicChart_sections_embedding (p : YChartAway) :
    yCubicChartRingEquiv (cubicEmbedding.app yAmbientAffineOpen
      (yAmbientChartRingIso.hom p)) = yChartToCurve p := by
  rw [Scheme.IdealSheafData.subschemeι_app]
  change yChartCubicEquiv
    ((Ideal.quotientEquiv yCubicChartIdeal (cubicIdealSheaf.ideal yAmbientAffineOpen)
      yAmbientChartRingIso.commRingCatIsoToRingEquiv yReducedChartIdeal_map.symm).symm
      ((cubicIdealSheaf.subschemeObjIso yAmbientAffineOpen).commRingCatIsoToRingEquiv
        ((cubicIdealSheaf.subschemeObjIso yAmbientAffineOpen).commRingCatIsoToRingEquiv.symm
          (Ideal.Quotient.mk (cubicIdealSheaf.ideal yAmbientAffineOpen)
            (yAmbientChartRingIso.commRingCatIsoToRingEquiv p))))) = _
  rw [RingEquiv.apply_symm_apply, Ideal.quotientEquiv_symm_mk, RingEquiv.symm_apply_apply]
  rfl

theorem yCubicChart_embedding_ring_square :
    yAmbientChartRingIso.hom ≫ cubicEmbedding.app yAmbientAffineOpen ≫
      yCubicChartRingEquiv.toCommRingCatIso.hom = CommRingCat.ofHom yChartToCurve := by
  ext p
  exact yCubicChart_sections_embedding p

theorem yCubicEmbedding_fromSpec : yReducedCubicOpen_isAffine.fromSpec ≫ cubicEmbedding =
    Spec.map (cubicEmbedding.app yAmbientAffineOpen) ≫ yAmbientAffineOpen.2.fromSpec := by
  simpa only [yReducedCubicOpen, Scheme.Hom.appLE_eq_app] using
    (IsAffineOpen.SpecMap_appLE_fromSpec cubicEmbedding
      yAmbientAffineOpen.2 yReducedCubicOpen_isAffine
      (show yReducedCubicOpen ≤ cubicEmbedding ⁻¹ᵁ yAmbientAffineOpen.1 from le_rfl)).symm

@[reassoc] theorem yCubicChart_embedding_scheme_square :
    yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι ≫ cubicEmbedding =
      Spec.map (CommRingCat.ofHom yChartToCurve) ≫
        Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num) := by
  change Spec.map yCubicChartRingEquiv.toCommRingCatIso.hom ≫
    yReducedCubicOpen_isAffine.fromSpec ≫ cubicEmbedding = _
  rw [yCubicEmbedding_fromSpec, ← Spec.map_comp_assoc]
  rw [← ySpecChart_fromSpec, ← Spec.map_comp_assoc]
  congr 1
  rw [← yCubicChart_embedding_ring_square, Iso.inv_hom_id_assoc]

#print axioms yCubicChart_embedding_ring_square
#print axioms yCubicEmbedding_fromSpec
#print axioms yCubicChart_embedding_scheme_square
end Holonics.Hodge.CMGraphSource
