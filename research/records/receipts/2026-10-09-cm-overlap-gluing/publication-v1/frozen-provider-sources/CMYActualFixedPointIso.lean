import CMYActualFixedChart
import CMYFixedPoint

/-! Identify the actual global fixed scheme pulled back to the Y chart with
the actual affine difference quotient, then with the complex point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def yActualFixedChartQuotientIso :
    yActualFixedChartFork.pt ≅ Spec (.of (YChartCubicRing ⧸ yFixedDifferenceIdeal)) :=
  yActualFixedChartFork_isLimit.conePointUniqueUpToIso
    (affineFixedFork_isLimit yIotaCoordinateRing)

def yActualFixedChartPointIso : yActualFixedChartFork.pt ≅ Spec (.of ℂ) :=
  yActualFixedChartQuotientIso ≪≫
    Scheme.Spec.mapIso (yFixedCoordinatePointEquiv.symm.toCommRingCatIso.op)

def yGlobalFixedPullbackPointIso :
    pullback cmFixedInclusion (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) ≅
      Spec (.of ℂ) :=
  eqToIso yActualFixedChart_point.symm ≪≫ yActualFixedChartPointIso

#print axioms yActualFixedChartQuotientIso
#print axioms yGlobalFixedPullbackPointIso
end Holonics.Hodge.CMGraphSource
