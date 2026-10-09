import CMYQuotientMap

/-! Exact affine coordinate generators for the actual reduced cubic Y chart.
These statements concern the constructed quotient map, not yet the projective
CM restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization Polynomial
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def yRatio (j : Fin 3) : YChartAway :=
  Away.mk CMGrading (coordinate_degree_one 1) 1 (MvPolynomial.X j)
    (by simpa using coordinate_degree_one j)

theorem yRatio_a_image : yAwayEquivPlane (yRatio 0) = MvPolynomial.X 0 := by
  change zAwayEquivPlane (yAwayToZ (yRatio 0)) = _
  rw [zAwayEquivPlane_apply, yRatio, yAwayToZ_mk 1 _ (coordinate_degree_one 0)]
  erw [zAwayToPlane_mk 1 _ (gradedSwapYZ.map_mem (coordinate_degree_one 0))]
  simp [zDehomogenize, gradedSwapYZ, swapYZ, Equiv.swap_apply_def]

theorem yRatio_b_image : yAwayEquivPlane (yRatio 2) = MvPolynomial.X 1 := by
  change zAwayEquivPlane (yAwayToZ (yRatio 2)) = _
  rw [zAwayEquivPlane_apply, yRatio, yAwayToZ_mk 1 _ (coordinate_degree_one 2)]
  erw [zAwayToPlane_mk 1 _ (gradedSwapYZ.map_mem (coordinate_degree_one 2))]
  simp [zDehomogenize, gradedSwapYZ, swapYZ, Equiv.swap_apply_def]

theorem yChartToCurve_ratio_a : yChartToCurve (yRatio 0) = AdjoinRoot.root yMonicCubic := by
  change Ideal.Quotient.mk (Ideal.span {yMonicCubic})
    (yChartBivariateEquiv (yRatio 0)) = _
  rw [yChartBivariateEquiv, RingEquiv.trans_apply, yRatio_a_image]
  change Ideal.Quotient.mk _ (yPlaneBivariateEquiv (MvPolynomial.X 0)) =
    Ideal.Quotient.mk _ Polynomial.X
  rw [yPlaneBivariateEquiv_a]

theorem yChartToCurve_ratio_b : yChartToCurve (yRatio 2) =
    AdjoinRoot.of yMonicCubic Polynomial.X := by
  change Ideal.Quotient.mk (Ideal.span {yMonicCubic})
    (yChartBivariateEquiv (yRatio 2)) = _
  rw [yChartBivariateEquiv, RingEquiv.trans_apply, yRatio_b_image]
  change Ideal.Quotient.mk _ (yPlaneBivariateEquiv (MvPolynomial.X 1)) =
    Ideal.Quotient.mk (Ideal.span {yMonicCubic}) (Polynomial.C (Polynomial.X : ℂ[X]))
  rw [yPlaneBivariateEquiv_b]

#print axioms yChartToCurve_ratio_a
#print axioms yChartToCurve_ratio_b
end Holonics.Hodge.CMGraphSource
