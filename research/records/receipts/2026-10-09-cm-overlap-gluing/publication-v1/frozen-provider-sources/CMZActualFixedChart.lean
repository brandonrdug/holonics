import CMZChartConjugacy
import CMProjectiveFixedPullback
import CMFixedChartLimit

/-! Actual Z restriction, with the same explicit associativity conversion as
the checked Y restriction. This consumes the preserved actual Z chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zActualChartInclusion_mono :
    Mono (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) := by infer_instance
attribute [local instance] zActualChartInclusion_mono

theorem zFixedChart_associated_square :
    Spec.map (CommRingCat.ofHom zIotaCoordinateRing) ≫
        (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) =
      (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ≫ cubicIotaHom := by
  rw [Category.assoc]
  exact zCubicChart_iota_inclusion_square.symm

def zActualFixedChartFork :
    Fork (Spec.map (CommRingCat.ofHom zIotaCoordinateRing))
      (𝟙 (Spec (.of ZChartSquareRing))) :=
  fixedChartFork cmFixedFork
    (zReducedCubicChartIso.inv ≫ zCubicOpen.ι)
    (Spec.map (CommRingCat.ofHom zIotaCoordinateRing))
    zFixedChart_associated_square

def zActualFixedChartFork_isLimit : IsLimit zActualFixedChartFork :=
  fixedChartFork_isLimit cmFixedFork cmFixedFork_isLimit
    (zReducedCubicChartIso.inv ≫ zCubicOpen.ι)
    (Spec.map (CommRingCat.ofHom zIotaCoordinateRing))
    zFixedChart_associated_square

theorem zActualFixedChart_point : zActualFixedChartFork.pt =
    pullback cmFixedInclusion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) := rfl

#print axioms zActualFixedChartFork_isLimit
#print axioms zActualFixedChart_point
end Holonics.Hodge.CMGraphSource
