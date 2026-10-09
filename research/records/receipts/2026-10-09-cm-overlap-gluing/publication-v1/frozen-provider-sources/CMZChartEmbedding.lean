import CMZCoordinateMap

/-! The proved Z chart isomorphism has its actual ambient inclusion square. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zCubicChart_sections_embedding (p : ZChartAway) :
    zCubicChartRingEquiv (cubicEmbedding.app zAmbientAffineOpen
      (zAmbientChartRingIso.hom p)) = zChartToCurve p := by
  rw [Scheme.IdealSheafData.subschemeι_app]
  change zChartSquareEquiv
    ((Ideal.quotientEquiv zCubicChartIdeal (cubicIdealSheaf.ideal zAmbientAffineOpen)
      zAmbientChartRingIso.commRingCatIsoToRingEquiv zAmbientChartIdeal_map.symm).symm
      ((cubicIdealSheaf.subschemeObjIso zAmbientAffineOpen).commRingCatIsoToRingEquiv
        ((cubicIdealSheaf.subschemeObjIso zAmbientAffineOpen).commRingCatIsoToRingEquiv.symm
          (Ideal.Quotient.mk (cubicIdealSheaf.ideal zAmbientAffineOpen)
            (zAmbientChartRingIso.commRingCatIsoToRingEquiv p))))) = _
  rw [RingEquiv.apply_symm_apply, Ideal.quotientEquiv_symm_mk, RingEquiv.symm_apply_apply]
  rfl

theorem zCubicChart_embedding_ring_square :
    zAmbientChartRingIso.hom ≫ cubicEmbedding.app zAmbientAffineOpen ≫
      zCubicChartRingEquiv.toCommRingCatIso.hom = CommRingCat.ofHom zChartToCurve := by
  ext p
  exact zCubicChart_sections_embedding p

theorem zCubicEmbedding_fromSpec : zCubicOpen_affine.fromSpec ≫ cubicEmbedding =
    Spec.map (cubicEmbedding.app zAmbientAffineOpen) ≫ zAmbientAffineOpen.2.fromSpec := by
  apply (cancel_epi zCubicOpen_affine.isoSpec.hom).mp
  rw [IsAffineOpen.isoSpec_hom]
  rw [IsAffineOpen.toSpecΓ_fromSpec_assoc, Scheme.Opens.toSpecΓ_naturality_assoc,
    IsAffineOpen.toSpecΓ_fromSpec]
  exact (morphismRestrict_ι cubicEmbedding zAmbientAffineOpen.1).symm

@[reassoc] theorem zCubicChart_embedding_scheme_square :
    zReducedCubicChartIso.inv ≫ zCubicOpen.ι ≫ cubicEmbedding =
      Spec.map (CommRingCat.ofHom zChartToCurve) ≫
        Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) := by
  change Spec.map zCubicChartRingEquiv.toCommRingCatIso.hom ≫
    zCubicOpen_affine.fromSpec ≫ cubicEmbedding = _
  rw [zCubicEmbedding_fromSpec, ← Spec.map_comp_assoc]
  rw [← zSpecChart_fromSpec, ← Spec.map_comp_assoc]
  congr 1
  rw [← zCubicChart_embedding_ring_square, Iso.inv_hom_id_assoc]

#print axioms zCubicChart_embedding_ring_square
#print axioms zCubicEmbedding_fromSpec
#print axioms zCubicChart_embedding_scheme_square
end Holonics.Hodge.CMGraphSource
