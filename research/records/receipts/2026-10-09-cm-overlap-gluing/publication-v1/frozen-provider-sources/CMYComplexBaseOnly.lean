import CMYChartEmbedding
import CMYScalarMap
import CMComplexGraphCore

/-! Exact retained Y complex-base proof body, with narrowed source imports. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

@[reassoc] theorem yActualChart_complex_base :
    (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) ≫ cmConcreteCubicBase =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ YChartCubicRing)) := by
  change (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) ≫
      (cubicEmbedding ≫ (Proj.toSpecZero CMGrading ≫ cmBaseIso.hom)) = _
  rw [← Category.assoc, Category.assoc yReducedCubicChartIso.inv,
    yCubicChart_embedding_scheme_square, Category.assoc,
    Proj.awayι_toSpecZero_assoc]
  change Spec.map (CommRingCat.ofHom yChartToCurve) ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom CMGrading (.powers yCoordinate))) ≫
      Spec.map (CommRingCat.ofHom cmDegreeZeroEquiv.symm.toRingHom) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact yChartToCurve_coefficient c

#print axioms yActualChart_complex_base
end Holonics.Hodge.CMGraphSource
