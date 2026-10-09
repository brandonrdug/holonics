import CMYCoordinateGenerators

/-! The descended actual homogeneous substitution on the reduced Y quotient
has the coordinate action a ↦ i*a, b ↦ -i*b. The projective-conjugacy equation
is proved separately; it is not an input to these coordinate calculations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization Polynomial
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yCoefficient_mk (c : ℂ) : yChartCoefficient c =
    Away.mk CMGrading (coordinate_degree_one 1) 0 (MvPolynomial.C c)
      (by simpa using chartConstant_degree_zero c) := rfl

theorem yAwayToPlane_coefficient (c : ℂ) :
    yAwayEquivPlane (yChartCoefficient c) = MvPolynomial.C c := by
  change zAwayEquivPlane (yAwayToZ (yChartCoefficient c)) = _
  rw [zAwayEquivPlane_apply, yCoefficient_mk, yAwayToZ_mk 0 _ (chartConstant_degree_zero c)]
  erw [zAwayToPlane_mk 0 _ (gradedSwapYZ.map_mem (chartConstant_degree_zero c))]
  simp [zDehomogenize, gradedSwapYZ, swapYZ]

theorem yChartToCurve_coefficient (c : ℂ) :
    yChartToCurve (yChartCoefficient c) = algebraMap ℂ YChartCubicRing c := by
  change Ideal.Quotient.mk (Ideal.span {yMonicCubic})
    (yChartBivariateEquiv (yChartCoefficient c)) = _
  rw [yChartBivariateEquiv, RingEquiv.trans_apply, yAwayToPlane_coefficient]
  change Ideal.Quotient.mk _ (yPlaneBivariateEquiv (MvPolynomial.C c)) = _
  have hc : yPlaneBivariateEquiv (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) :=
    yPlaneBivariateEquiv.commutes c
  rw [hc]
  rfl

theorem yAwayIota_ratio_a : yAwayIota (yRatio 0) = yChartCoefficient Complex.I * yRatio 0 := by
  rw [yRatio, yAwayIota_mk 1 _ (coordinate_degree_one 0)]
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [Away.val_mk, gradedIota, homogeneousIota, homogeneousPullback,
    yChartCoefficient, fromZeroRingHom, cmDegreeZeroEquiv, Localization.mk_mul] <;>
    congr 1 <;> ring

theorem yAwayIota_ratio_b : yAwayIota (yRatio 2) = yChartCoefficient (-Complex.I) * yRatio 2 := by
  rw [yRatio, yAwayIota_mk 1 _ (coordinate_degree_one 2)]
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [Away.val_mk, gradedIota, homogeneousIota, homogeneousPullback,
    yChartCoefficient, fromZeroRingHom, cmDegreeZeroEquiv, Localization.mk_mul] <;>
    congr 1 <;> ring

theorem yIotaCoordinateRing_a : yIotaCoordinateRing (AdjoinRoot.root yMonicCubic) =
    algebraMap ℂ YChartCubicRing Complex.I * AdjoinRoot.root yMonicCubic := by
  have he := congrArg (fun f : YChartAway →+* YChartCubicRing => f (yRatio 0))
    yIota_coordinate_quotient_square
  simpa only [RingHom.comp_apply, yChartToCurve_ratio_a, yAwayIota_ratio_a,
    map_mul, yChartToCurve_coefficient] using he

theorem yIotaCoordinateRing_b : yIotaCoordinateRing (AdjoinRoot.of yMonicCubic Polynomial.X) =
    algebraMap ℂ YChartCubicRing (-Complex.I) * AdjoinRoot.of yMonicCubic Polynomial.X := by
  have he := congrArg (fun f : YChartAway →+* YChartCubicRing => f (yRatio 2))
    yIota_coordinate_quotient_square
  simpa only [RingHom.comp_apply, yChartToCurve_ratio_b, yAwayIota_ratio_b,
    map_mul, yChartToCurve_coefficient] using he

#print axioms yIotaCoordinateRing_a
#print axioms yIotaCoordinateRing_b
end Holonics.Hodge.CMGraphSource
