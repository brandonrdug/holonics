import CMZCoordinateMap

/-! The actual Z-chart map fixes the complex base, including after quotient transport. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open HomogeneousLocalization Polynomial
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zAwayIota_coefficient (c : ℂ) :
    zAwayIota (zChartCoefficient c) = zChartCoefficient c := by
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [zAwayIota, zChartCoefficient, HomogeneousLocalization.map,
    fromZeroRingHom, cmDegreeZeroEquiv, gradedIota, homogeneousIota, homogeneousPullback]

theorem zIotaCoordinateRing_coefficient (c : ℂ) :
    zIotaCoordinateRing (algebraMap ℂ ZChartSquareRing c) = algebraMap ℂ ZChartSquareRing c := by
  have he := congrArg (fun f : ZChartAway →+* ZChartSquareRing => f (zChartCoefficient c))
    zIota_coordinate_quotient_square
  simpa only [RingHom.comp_apply, zChartToCurve_coefficient, zAwayIota_coefficient] using he

def zIotaAlgebraMap : ZChartSquareRing →ₐ[ℂ] ZChartSquareRing where
  __ := zIotaCoordinateRing
  commutes' := zIotaCoordinateRing_coefficient

theorem zCoordinateAlgebraMap_ext {A : Type*} [CommRing A] [Algebra ℂ A]
    {f g : ZChartSquareRing →ₐ[ℂ] A}
    (hu : f (AdjoinRoot.of squareCurve.toAffine.polynomial X) =
      g (AdjoinRoot.of squareCurve.toAffine.polynomial X))
    (hv : f (AdjoinRoot.root squareCurve.toAffine.polynomial) =
      g (AdjoinRoot.root squareCurve.toAffine.polynomial)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    exact hu
  · exact hv

#print axioms zAwayIota_coefficient
#print axioms zIotaCoordinateRing_coefficient
#print axioms zCoordinateAlgebraMap_ext
end Holonics.Hodge.CMGraphSource
