import CMZChartEmbedding
import CMComplexGraphCore

/-! Exact retained Z complex-base proof body, with only its source imports.
Provenance is recorded in narrow-owner-provenance.json. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

@[reassoc] theorem zActualChart_complex_base :
    (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ≫ cmConcreteCubicBase =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ ZChartSquareRing)) := by
  change (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ≫
      (cubicEmbedding ≫ (Proj.toSpecZero CMGrading ≫ cmBaseIso.hom)) = _
  rw [← Category.assoc, Category.assoc zReducedCubicChartIso.inv,
    zCubicChart_embedding_scheme_square, Category.assoc,
    Proj.awayι_toSpecZero_assoc]
  change Spec.map (CommRingCat.ofHom zChartToCurve) ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom CMGrading (.powers zCoordinate))) ≫
      Spec.map (CommRingCat.ofHom cmDegreeZeroEquiv.symm.toRingHom) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact zChartToCurve_coefficient c

#print axioms zActualChart_complex_base
end Holonics.Hodge.CMGraphSource
