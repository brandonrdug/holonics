import CMYFixedSquareAssociated
import CMProjectiveFixedPullback
import CMFixedChartLimit

/-! Actual chart restriction of the global graph-diagonal fixed scheme.
The checked associated square removes the expensive implicit conversion.
This constructs and checks its universal property, not merely a coordinate
ideal or a cone with a limit assumed as a field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] yActualChartInclusion_mono

def yActualFixedChartFork :
    Fork (Spec.map (CommRingCat.ofHom yIotaCoordinateRing))
      (𝟙 (Spec (.of YChartCubicRing))) :=
  fixedChartFork cmFixedFork
    (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι)
    (Spec.map (CommRingCat.ofHom yIotaCoordinateRing))
    yFixedChart_associated_square

def yActualFixedChartFork_isLimit : IsLimit yActualFixedChartFork :=
  fixedChartFork_isLimit cmFixedFork cmFixedFork_isLimit
    (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι)
    (Spec.map (CommRingCat.ofHom yIotaCoordinateRing))
    yFixedChart_associated_square

theorem yActualFixedChart_point : yActualFixedChartFork.pt =
    pullback cmFixedInclusion (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) := rfl

#print axioms yActualFixedChartFork_isLimit
#print axioms yActualFixedChart_point
end Holonics.Hodge.CMGraphSource
