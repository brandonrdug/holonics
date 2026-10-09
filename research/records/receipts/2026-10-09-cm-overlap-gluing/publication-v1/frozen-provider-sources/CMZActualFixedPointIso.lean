import CMZActualFixedChart
import CMZFixedPoint

/-! Actual global fixed scheme pulled back to Z is the complex point, via
the proved universal properties and the actual difference-ideal quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def zActualFixedChartQuotientIso :
    zActualFixedChartFork.pt ≅ Spec (.of (ZChartSquareRing ⧸ zFixedDifferenceIdeal)) :=
  zActualFixedChartFork_isLimit.conePointUniqueUpToIso
    (affineFixedFork_isLimit zIotaCoordinateRing)

def zActualFixedChartPointIso : zActualFixedChartFork.pt ≅ Spec (.of ℂ) :=
  zActualFixedChartQuotientIso ≪≫
    Scheme.Spec.mapIso (zFixedCoordinatePointEquiv.symm.toCommRingCatIso.op)

def zGlobalFixedPullbackPointIso :
    pullback cmFixedInclusion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ≅ Spec (.of ℂ) :=
  eqToIso zActualFixedChart_point.symm ≪≫ zActualFixedChartPointIso

theorem zActualFixedChartQuotientIso_hom_inclusion :
    zActualFixedChartQuotientIso.hom ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk zFixedDifferenceIdeal)) =
      pullback.snd cmFixedInclusion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) :=
  IsLimit.conePointUniqueUpToIso_hom_comp zActualFixedChartFork_isLimit
    (affineFixedFork_isLimit zIotaCoordinateRing) WalkingParallelPair.zero

theorem zActualFixedChartQuotientIso_inv_inclusion :
    zActualFixedChartQuotientIso.inv ≫
      pullback.snd cmFixedInclusion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk zFixedDifferenceIdeal)) :=
  IsLimit.conePointUniqueUpToIso_inv_comp zActualFixedChartFork_isLimit
    (affineFixedFork_isLimit zIotaCoordinateRing) WalkingParallelPair.zero

#print axioms zGlobalFixedPullbackPointIso
#print axioms zActualFixedChartQuotientIso_inv_inclusion
end Holonics.Hodge.CMGraphSource
