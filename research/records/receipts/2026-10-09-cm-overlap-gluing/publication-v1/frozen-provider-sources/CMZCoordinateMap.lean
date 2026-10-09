import CMZCoordinateStability
import CMSourceOverlap

/-! The actual degree-zero Z chart CM pullback and its quotient coordinate map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization Polynomial
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def zAwayIota : ZChartAway →+* ZChartAway :=
  HomogeneousLocalization.map gradedIota (by
    rintro p ⟨n, rfl⟩
    exact ⟨n, by simp⟩)
theorem zAwayIota_mk (n : ℕ) (p : HomogeneousRing) (hp : p ∈ CMGrading n) :
    zAwayIota (Away.mk CMGrading (coordinate_degree_one 2) n p (by simpa using hp)) =
      Away.mk CMGrading (coordinate_degree_one 2) n (gradedIota p)
        (by simpa using gradedIota.map_mem hp) := by
  unfold zAwayIota Away.mk
  rw [HomogeneousLocalization.map_mk]
  congr 1
  simp [map_pow]

theorem zAwayIota_cubic : zAwayIota zNormalizedCubic = -zNormalizedCubic := by
  rw [zNormalizedCubic, zAwayIota_mk 3 _ cubic_degree_three]
  have he : gradedIota projectiveCubic = -projectiveCubic :=
    by
      change homogeneousPullback Complex.I projectiveCubic = _
      exact homogeneousPullback_cubic Complex.I Complex.I_sq
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [Away.val_mk, he, zCoordinate, Localization.neg_mk]

def zIotaQuotient : ZCubicQuotient →+* ZCubicQuotient :=
  Ideal.quotientMap zCubicChartIdeal zAwayIota (by
    rw [zCubicChartIdeal, Ideal.span_le, Set.singleton_subset_iff]
    change zAwayIota zNormalizedCubic ∈ zCubicChartIdeal
    rw [zAwayIota_cubic]
    exact neg_mem (Ideal.subset_span (Set.mem_singleton _)))
def zIotaCoordinateRing : ZChartSquareRing →+* ZChartSquareRing :=
  zChartSquareEquiv.toRingHom.comp (zIotaQuotient.comp zChartSquareEquiv.symm.toRingHom)
def zChartToCurve : ZChartAway →+* ZChartSquareRing :=
  zChartSquareEquiv.toRingHom.comp (Ideal.Quotient.mk zCubicChartIdeal)

theorem zIota_coordinate_quotient_square :
    zIotaCoordinateRing.comp zChartToCurve = zChartToCurve.comp zAwayIota := by
  ext p
  simp [zIotaCoordinateRing, zChartToCurve, zIotaQuotient]

theorem zChartToCurve_ratio_u : zChartToCurve (zRatio 0) =
    AdjoinRoot.of squareCurve.toAffine.polynomial Polynomial.X := by
  change Ideal.Quotient.mk (Ideal.span {squareCurve.toAffine.polynomial})
    (zChartBivariateEquiv (zRatio 0)) = _
  rw [zChartBivariateEquiv, RingEquiv.trans_apply, zAwayEquivPlane_apply, zAwayToPlane_ratio]
  simp only [Matrix.cons_val_zero]
  change Ideal.Quotient.mk _ (zPlaneBivariateEquiv (MvPolynomial.X 0)) = _
  rw [zPlaneBivariateEquiv_x]
  rfl
theorem zChartToCurve_ratio_v : zChartToCurve (zRatio 1) =
    AdjoinRoot.root squareCurve.toAffine.polynomial := zChartSquareEquiv_overlapDenominator

theorem zAwayIota_ratio_u : zAwayIota (zRatio 0) = -zRatio 0 := by
  rw [zRatio, zAwayIota_mk 1 _ (coordinate_degree_one 0)]
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [Away.val_mk, gradedIota, homogeneousIota, homogeneousPullback, Localization.neg_mk]

theorem zAwayIota_ratio_v : zAwayIota (zRatio 1) = zChartCoefficient Complex.I * zRatio 1 := by
  rw [zRatio, zAwayIota_mk 1 _ (coordinate_degree_one 1)]
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [Away.val_mk, gradedIota, homogeneousIota, homogeneousPullback,
    zChartCoefficient, fromZeroRingHom, cmDegreeZeroEquiv, Localization.mk_mul]

theorem zChartToCurve_coefficient (c : ℂ) :
    zChartToCurve (zChartCoefficient c) = algebraMap ℂ ZChartSquareRing c := by
  change Ideal.Quotient.mk (Ideal.span {squareCurve.toAffine.polynomial})
    (zChartBivariateEquiv (zChartCoefficient c)) = _
  rw [zChartBivariateEquiv, RingEquiv.trans_apply, zAwayEquivPlane_apply, zAwayToPlane_coefficient]
  change Ideal.Quotient.mk _ (zPlaneBivariateEquiv (MvPolynomial.C c)) = _
  have hc : zPlaneBivariateEquiv (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) :=
    zPlaneBivariateEquiv.commutes c
  rw [hc]
  rfl

theorem zIotaCoordinateRing_u : zIotaCoordinateRing
    (AdjoinRoot.of squareCurve.toAffine.polynomial Polynomial.X) =
      -AdjoinRoot.of squareCurve.toAffine.polynomial Polynomial.X := by
  have he := congrArg (fun f : ZChartAway →+* ZChartSquareRing => f (zRatio 0))
    zIota_coordinate_quotient_square
  simpa only [RingHom.comp_apply, zChartToCurve_ratio_u, zAwayIota_ratio_u, map_neg] using he
theorem zIotaCoordinateRing_v : zIotaCoordinateRing
    (AdjoinRoot.root squareCurve.toAffine.polynomial) =
      algebraMap ℂ ZChartSquareRing Complex.I * AdjoinRoot.root squareCurve.toAffine.polynomial := by
  have he := congrArg (fun f : ZChartAway →+* ZChartSquareRing => f (zRatio 1))
    zIota_coordinate_quotient_square
  simpa only [RingHom.comp_apply, zChartToCurve_ratio_v, zAwayIota_ratio_v,
    map_mul, zChartToCurve_coefficient] using he

#print axioms zAwayIota
#print axioms zIota_coordinate_quotient_square
#print axioms zChartToCurve_ratio_u
#print axioms zChartToCurve_ratio_v
#print axioms zIotaCoordinateRing_u
#print axioms zIotaCoordinateRing_v
end Holonics.Hodge.CMGraphSource
