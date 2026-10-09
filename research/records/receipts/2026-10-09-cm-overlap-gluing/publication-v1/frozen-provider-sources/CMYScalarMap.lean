import CMYCoordinateAction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open HomogeneousLocalization Polynomial
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yAwayIota_coefficient (c : ℂ) : yAwayIota (yChartCoefficient c) = yChartCoefficient c := by
  rw [yCoefficient_mk, yAwayIota_mk 0 _ (chartConstant_degree_zero c)]
  have hc : gradedIota (MvPolynomial.C c) = MvPolynomial.C c := homogeneousIota.commutes c
  simp only [hc, pow_zero, mul_one]

theorem yIotaCoordinateRing_coefficient (c : ℂ) :
    yIotaCoordinateRing (algebraMap ℂ YChartCubicRing c) = algebraMap ℂ YChartCubicRing c := by
  have he := congrArg (fun f : YChartAway →+* YChartCubicRing => f (yChartCoefficient c))
    yIota_coordinate_quotient_square
  simpa only [RingHom.comp_apply, yChartToCurve_coefficient, yAwayIota_coefficient] using he

def yIotaAlgebraMap : YChartCubicRing →ₐ[ℂ] YChartCubicRing where
  __ := yIotaCoordinateRing
  commutes' := yIotaCoordinateRing_coefficient

theorem yCoordinateAlgebraMap_ext {A : Type*} [CommRing A] [Algebra ℂ A]
    {f g : YChartCubicRing →ₐ[ℂ] A}
    (hb : f (AdjoinRoot.of yMonicCubic X) = g (AdjoinRoot.of yMonicCubic X))
    (ha : f (AdjoinRoot.root yMonicCubic) = g (AdjoinRoot.root yMonicCubic)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    exact hb
  · exact ha

#print axioms yIotaCoordinateRing_coefficient
#print axioms yCoordinateAlgebraMap_ext
end Holonics.Hodge.CMGraphSource
