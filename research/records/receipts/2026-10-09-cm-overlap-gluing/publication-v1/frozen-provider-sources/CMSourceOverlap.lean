import CMDegreeZeroOverlap
import CMZChartReduced
import Mathlib.RingTheory.Localization.Ideal

/-!
The cubic quotient on the actual degree-zero overlap is the localization
of its proved Z-chart quotient. The denominator maps to the Weierstrass
root v. This is a ring comparison; the projective restriction square and
the graph/diagonal fixed scheme have not been inferred from it.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open HomogeneousLocalization AlgebraicGeometry Polynomial
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ZCubicQuotient := ZChartAway ⧸ zCubicChartIdeal
def yzCubicChartIdeal : Ideal YZDegreeZeroAway :=
  zCubicChartIdeal.map zToDegreeZeroOverlap
abbrev YZCubicQuotient := YZDegreeZeroAway ⧸ yzCubicChartIdeal
def zQuotientOverlapDenominator : ZCubicQuotient :=
  Ideal.Quotient.mk zCubicChartIdeal (zRatio 1)

instance sourceOverlapAlgebra : Algebra ZCubicQuotient YZCubicQuotient :=
  Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
    zCubicChartIdeal ≤ yzCubicChartIdeal.comap (algebraMap ZChartAway YZDegreeZeroAway))

theorem sourceOverlap_isLocalization :
    IsLocalization.Away zQuotientOverlapDenominator YZCubicQuotient := by
  let := degreeZeroOverlap_isLocalization_z
  have h : IsLocalization (Algebra.algebraMapSubmonoid ZCubicQuotient (.powers (zRatio 1)))
      YZCubicQuotient := inferInstanceAs (IsLocalization
        (Algebra.algebraMapSubmonoid ZCubicQuotient (.powers (zRatio 1)))
        (YZDegreeZeroAway ⧸ zCubicChartIdeal.map (algebraMap ZChartAway YZDegreeZeroAway)))
  simpa [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
    zQuotientOverlapDenominator, Ideal.Quotient.algebraMap_eq] using h

def sourceOverlapEquivQuotientLocalization :
    YZCubicQuotient ≃ₐ[ZCubicQuotient] Localization.Away zQuotientOverlapDenominator := by
  letI := sourceOverlap_isLocalization
  exact IsLocalization.algEquiv (.powers zQuotientOverlapDenominator) _ _

theorem zChartSquareEquiv_overlapDenominator :
    zChartSquareEquiv zQuotientOverlapDenominator =
      AdjoinRoot.root squareCurve.toAffine.polynomial := by
  change Ideal.Quotient.mk (Ideal.span {squareCurve.toAffine.polynomial})
    (zChartBivariateEquiv (zRatio 1)) = _
  rw [zChartBivariateEquiv, RingEquiv.trans_apply, zAwayEquivPlane_apply,
    zAwayToPlane_ratio]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  change Ideal.Quotient.mk (Ideal.span {squareCurve.toAffine.polynomial})
    (zPlaneBivariateEquiv (MvPolynomial.X 1)) = _
  rw [zPlaneBivariateEquiv_y]
  rfl

def sourceOverlapEquivWeierstrassLocalization :
    YZCubicQuotient ≃+* Localization.Away (AdjoinRoot.root squareCurve.toAffine.polynomial) := by
  letI := sourceOverlap_isLocalization
  exact IsLocalization.ringEquivOfRingEquiv YZCubicQuotient
    (Localization.Away (AdjoinRoot.root squareCurve.toAffine.polynomial))
    zChartSquareEquiv (M := .powers zQuotientOverlapDenominator)
      (T := .powers (AdjoinRoot.root squareCurve.toAffine.polynomial)) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers zChartSquareEquiv_overlapDenominator)

#print axioms sourceOverlap_isLocalization
#print axioms sourceOverlapEquivQuotientLocalization
#print axioms zChartSquareEquiv_overlapDenominator
#print axioms sourceOverlapEquivWeierstrassLocalization
end Holonics.Hodge.CMGraphSource
