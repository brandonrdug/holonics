import CMYActualFixedPointIso

/-! The quotient comparison respects the actual chart inclusion map; this
compatibility is needed when excluding the overlap of the global fixed opens. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yActualFixedChartQuotientIso_hom_inclusion :
    yActualFixedChartQuotientIso.hom ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk yFixedDifferenceIdeal)) =
      pullback.snd cmFixedInclusion (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) :=
  IsLimit.conePointUniqueUpToIso_hom_comp yActualFixedChartFork_isLimit
    (affineFixedFork_isLimit yIotaCoordinateRing) WalkingParallelPair.zero

theorem yActualFixedChartQuotientIso_inv_inclusion :
    yActualFixedChartQuotientIso.inv ≫
      pullback.snd cmFixedInclusion (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk yFixedDifferenceIdeal)) :=
  IsLimit.conePointUniqueUpToIso_inv_comp yActualFixedChartFork_isLimit
    (affineFixedFork_isLimit yIotaCoordinateRing) WalkingParallelPair.zero

#print axioms yActualFixedChartQuotientIso_hom_inclusion
#print axioms yActualFixedChartQuotientIso_inv_inclusion
end Holonics.Hodge.CMGraphSource
