import CMZChartEmbedding
import CMZAmbientMap

/-! Coordinate-map conjugacy under the proved actual reduced cubic Z chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zCubicChart_iota_inclusion_square :
    zReducedCubicChartIso.inv ≫ zCubicOpen.ι ≫ cubicIotaHom =
      Spec.map (CommRingCat.ofHom zIotaCoordinateRing) ≫
        zReducedCubicChartIso.inv ≫ zCubicOpen.ι := by
  apply (cancel_mono cubicEmbedding).mp
  have hc : CommRingCat.ofHom zAwayIota ≫ CommRingCat.ofHom zChartToCurve =
      CommRingCat.ofHom zChartToCurve ≫ CommRingCat.ofHom zIotaCoordinateRing := by
    apply CommRingCat.hom_ext
    exact zIota_coordinate_quotient_square.symm
  simp only [Category.assoc]
  rw [cubicIotaHom_embedding, zCubicChart_embedding_scheme_square_assoc,
    zCubicChart_embedding_scheme_square, zAwayIota_ambient_square,
    ← Spec.map_comp_assoc, hc, Spec.map_comp_assoc]

#print axioms zCubicChart_iota_inclusion_square
end Holonics.Hodge.CMGraphSource
