import CMZChartReduced

/-!
An actual affine-open chart of the reduced projective cubic is identified
with Spec of its Weierstrass coordinate ring. The ideal equality is the
proved reduced chart comparison, not an input to this construction.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev zCubicOpen : CMProjectiveCubic.Opens := cubicEmbedding ⁻¹ᵁ zAmbientAffineOpen.1
theorem zCubicOpen_affine : IsAffineOpen zCubicOpen :=
  zAmbientAffineOpen.2.preimage cubicEmbedding

theorem zAmbientChartIdeal_map :
    zCubicChartIdeal.map zAmbientChartRingIso.hom.hom = cubicIdealSheaf.ideal zAmbientAffineOpen := by
  rw [← zReducedChartIdeal]
  exact Ideal.map_comap_of_surjective _ zAmbientChartRingIso.commRingCatIsoToRingEquiv.surjective _

def zCubicChartRingEquiv : Γ(CMProjectiveCubic, zCubicOpen) ≃+* ZChartSquareRing :=
  (cubicIdealSheaf.subschemeObjIso zAmbientAffineOpen).commRingCatIsoToRingEquiv.trans
    ((Ideal.quotientEquiv zCubicChartIdeal (cubicIdealSheaf.ideal zAmbientAffineOpen)
      zAmbientChartRingIso.commRingCatIsoToRingEquiv zAmbientChartIdeal_map.symm).symm.trans
        zChartSquareEquiv)

def zReducedCubicChartIso : zCubicOpen.toScheme ≅ Spec (.of ZChartSquareRing) :=
  zCubicOpen_affine.isoSpec ≪≫
    Scheme.Spec.mapIso (zCubicChartRingEquiv.symm.toCommRingCatIso.op)

#print axioms zCubicOpen_affine
#print axioms zAmbientChartIdeal_map
#print axioms zCubicChartRingEquiv
#print axioms zReducedCubicChartIso
end Holonics.Hodge.CMGraphSource
