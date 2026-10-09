import CMYChartEmbedding
import CMYAmbientFromSections

/-! Coordinate-map conjugacy under the proved actual reduced cubic Y chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yCubicChart_iota_inclusion_square :
    yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι ≫ cubicIotaHom =
      Spec.map (CommRingCat.ofHom yIotaCoordinateRing) ≫
        yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι := by
  apply (cancel_mono cubicEmbedding).mp
  have hc : CommRingCat.ofHom yAwayIota ≫ CommRingCat.ofHom yChartToCurve =
      CommRingCat.ofHom yChartToCurve ≫ CommRingCat.ofHom yIotaCoordinateRing := by
    apply CommRingCat.hom_ext
    exact yIota_coordinate_quotient_square.symm
  simp only [Category.assoc]
  rw [cubicIotaHom_embedding, yCubicChart_embedding_scheme_square_assoc,
    yCubicChart_embedding_scheme_square, yAwayIota_ambient_square,
    ← Spec.map_comp_assoc, hc, Spec.map_comp_assoc]

#print axioms yCubicChart_iota_inclusion_square
end Holonics.Hodge.CMGraphSource
