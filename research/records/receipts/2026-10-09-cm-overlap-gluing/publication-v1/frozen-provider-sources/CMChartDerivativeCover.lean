import CMYChartReduced
import CMGraphSource
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Concrete Bezout identities for F=a^3-a*b^2-b and G=v^2-u^3+u.
The actual quotient conventions are used. The G identity is also checked
with the proposed rational coefficients over C; its denominator-cleared
form provides the derivative-face coverage on the actual source ring.
No scheme smoothness or intersection-number claim follows by definition. -/
noncomputable section
open Polynomial
namespace Holonics.Hodge.CMGraphSource

abbrev yDerivativeA : YChartCubicRing := AdjoinRoot.root yMonicCubic
abbrev yDerivativeB : YChartCubicRing := AdjoinRoot.of yMonicCubic X
def yPartialA : YChartCubicRing := 3 * yDerivativeA ^ 2 - yDerivativeB ^ 2
def yPartialB : YChartCubicRing := -2 * yDerivativeA * yDerivativeB - 1
def zPartialU : CurveRing := 1 - 3 * u ^ 2
def zPartialV : CurveRing := 2 * v

theorem yDerivative_polynomial_identity {R : Type*} [CommRing R] (a b : R) :
    3 * a * (a ^ 3 - a * b ^ 2 - b) - a ^ 2 * (3 * a ^ 2 - b ^ 2) -
      (1 + a * b) * (-2 * a * b - 1) = 1 := by ring

theorem zDerivative_polynomial_identity {R : Type*} [CommRing R] (u v : R) :
    18 * u * (v ^ 2 - u ^ 3 + u) + (4 - 6 * u ^ 2) * (1 - 3 * u ^ 2) -
      9 * u * v * (2 * v) = 4 := by ring

theorem zDerivative_rational_identity (u v : ℂ) :
    (9 / 2 : ℂ) * u * (v ^ 2 - u ^ 3 + u) +
      (1 - (3 / 2 : ℂ) * u ^ 2) * (1 - 3 * u ^ 2) -
      (9 / 4 : ℂ) * u * v * (2 * v) = 1 := by ring

theorem yDerivative_source_relation :
    yDerivativeA ^ 3 - yDerivativeA * yDerivativeB ^ 2 - yDerivativeB = 0 := by
  have h := AdjoinRoot.eval₂_root yMonicCubic
  conv at h => arg 1; arg 3; rw [yMonicCubic]
  simp only [eval₂_sub, eval₂_pow, eval₂_mul, eval₂_C, eval₂_X, map_pow] at h
  change yDerivativeA ^ 3 - yDerivativeB ^ 2 * yDerivativeA - yDerivativeB = 0 at h
  simpa only [mul_comm] using h

theorem yDerivative_source_bezout :
    -yDerivativeA ^ 2 * yPartialA - (1 + yDerivativeA * yDerivativeB) * yPartialB = 1 := by
  have h := yDerivative_polynomial_identity yDerivativeA yDerivativeB
  rw [yDerivative_source_relation, mul_zero, zero_sub] at h
  simpa only [yPartialA, yPartialB, neg_mul] using h

theorem zDerivative_source_bezout :
    (4 - 6 * u ^ 2) * zPartialU - 9 * u * v * zPartialV = 4 := by
  have h := zDerivative_polynomial_identity u v
  have hG : v ^ 2 - u ^ 3 + u = 0 := by rw [curve_relation]; ring
  rw [hG, mul_zero, zero_add] at h
  exact h

theorem yDerivative_ideal_top :
    Ideal.span ({yPartialA, yPartialB} : Set YChartCubicRing) = ⊤ := by
  let J : Ideal YChartCubicRing := Ideal.span {yPartialA, yPartialB}
  apply Ideal.eq_top_of_isUnit_mem J _ isUnit_one
  rw [← yDerivative_source_bezout]
  exact J.sub_mem
    (J.mul_mem_left _ (Ideal.subset_span (Set.mem_insert _ _)))
    (J.mul_mem_left _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem zDerivative_ideal_top : Ideal.span ({zPartialU, zPartialV} : Set CurveRing) = ⊤ := by
  let J : Ideal CurveRing := Ideal.span {zPartialU, zPartialV}
  have hfour : (4 : CurveRing) ∈ J := by
    rw [← zDerivative_source_bezout]
    exact J.sub_mem
      (J.mul_mem_left _ (Ideal.subset_span (Set.mem_insert _ _)))
      (J.mul_mem_left _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hu : IsUnit (4 : CurveRing) := by
    have h := (isUnit_iff_ne_zero.mpr (by norm_num : (4 : ℂ) ≠ 0)).map (algebraMap ℂ CurveRing)
    simpa only [map_ofNat] using h
  exact Ideal.eq_top_of_isUnit_mem J hfour hu

theorem yDerivative_faces_cover :
    (⨆ p ∈ ({yPartialA, yPartialB} : Set YChartCubicRing), PrimeSpectrum.basicOpen p) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr yDerivative_ideal_top

theorem zDerivative_faces_cover :
    (⨆ p ∈ ({zPartialU, zPartialV} : Set CurveRing), PrimeSpectrum.basicOpen p) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr zDerivative_ideal_top

#print axioms yDerivative_polynomial_identity
#print axioms zDerivative_polynomial_identity
#print axioms zDerivative_rational_identity
#print axioms yDerivative_source_relation
#print axioms yDerivative_source_bezout
#print axioms zDerivative_source_bezout
#print axioms yDerivative_faces_cover
#print axioms zDerivative_faces_cover
end Holonics.Hodge.CMGraphSource
