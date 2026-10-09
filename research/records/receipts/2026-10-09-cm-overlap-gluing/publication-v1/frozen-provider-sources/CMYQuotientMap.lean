import CMYDirectDenominator
import CMYChartReduced

/-! The constructed Y CM map descends through the proved reduced chart
quotient. Its comparison with the actual projective map is still separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev YCubicQuotient := YChartAway ⧸ yCubicChartIdeal
def yChartCoefficient : ℂ →+* YChartAway :=
  (fromZeroRingHom CMGrading (.powers yCoordinate)).comp cmDegreeZeroEquiv.symm.toRingHom

theorem yAwayIota_cubic : yAwayIota yNormalizedCubic =
    yChartCoefficient (-Complex.I) * yNormalizedCubic := by
  rw [yNormalizedCubic, yAwayIota_mk 3 _ cubic_degree_three]
  have he : gradedIota projectiveCubic = -projectiveCubic := by
    change homogeneousPullback Complex.I projectiveCubic = _
    exact homogeneousPullback_cubic Complex.I Complex.I_sq
  have hcube : (-Complex.I) ^ 3 = Complex.I := by
    calc
      (-Complex.I) ^ 3 = (-Complex.I) * ((-Complex.I) ^ 2) := by ring
      _ = Complex.I := by simp [Complex.I_sq]
  have hpoly : gradedIota projectiveCubic * MvPolynomial.C (-Complex.I) ^ 3 =
      MvPolynomial.C (-Complex.I) * projectiveCubic := by
    rw [he, ← MvPolynomial.C_pow, hcube, MvPolynomial.C_neg]
    ring
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [Away.val_mk, yChartCoefficient, fromZeroRingHom,
    cmDegreeZeroEquiv, Localization.mk_mul, mul_comm]
  simp only [← MvPolynomial.C_neg, ← MvPolynomial.C_pow, hcube, he]
  congr 1
  ring

def yIotaQuotient : YCubicQuotient →+* YCubicQuotient :=
  Ideal.quotientMap yCubicChartIdeal yAwayIota (by
    rw [yCubicChartIdeal, Ideal.span_le, Set.singleton_subset_iff]
    change yAwayIota yNormalizedCubic ∈ yCubicChartIdeal
    rw [yAwayIota_cubic]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
def yIotaCoordinateRing : YChartCubicRing →+* YChartCubicRing :=
  yChartCubicEquiv.toRingHom.comp (yIotaQuotient.comp yChartCubicEquiv.symm.toRingHom)
def yChartToCurve : YChartAway →+* YChartCubicRing :=
  yChartCubicEquiv.toRingHom.comp (Ideal.Quotient.mk yCubicChartIdeal)

theorem yIota_coordinate_quotient_square :
    yIotaCoordinateRing.comp yChartToCurve = yChartToCurve.comp yAwayIota := by
  ext p
  simp [yIotaCoordinateRing, yChartToCurve, yIotaQuotient]

#print axioms yAwayIota_cubic
#print axioms yIota_coordinate_quotient_square
end Holonics.Hodge.CMGraphSource
