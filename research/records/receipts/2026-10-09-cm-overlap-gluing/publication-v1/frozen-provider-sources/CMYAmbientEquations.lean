import CMYScalarMap
import CMChartDerivativeCover
import Mathlib.RingTheory.TensorProduct.Basic

/-! Actual Y tensor-product graph and diagonal ideals, with their two
source equations and the two denominator faces supplied by subtraction. -/
noncomputable section
open scoped TensorProduct
open Polynomial
namespace Holonics.Hodge.CMGraphSource

instance yCurveRing_domain : IsDomain YChartCubicRing :=
  AdjoinRoot.isDomain_of_prime yMonicCubic_irreducible.prime
abbrev YProductRing := YChartCubicRing ⊗[ℂ] YChartCubicRing
abbrev yAmbientA : YChartCubicRing := AdjoinRoot.root yMonicCubic
abbrev yAmbientB : YChartCubicRing := AdjoinRoot.of yMonicCubic X
def yLeft : YChartCubicRing →ₐ[ℂ] YProductRing := Algebra.TensorProduct.includeLeft
def yRight : YChartCubicRing →ₐ[ℂ] YProductRing := Algebra.TensorProduct.includeRight
def yGraphReceiver : YProductRing →ₐ[ℂ] YChartCubicRing :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ YChartCubicRing) yIotaAlgebraMap (fun _ _ => Commute.all _ _)
def yDiagonalReceiver : YProductRing →ₐ[ℂ] YChartCubicRing := Algebra.TensorProduct.lmul' ℂ
abbrev yAmbientPhase : YProductRing := algebraMap ℂ YProductRing Complex.I

def yGraphAEquation : YProductRing := yRight yAmbientA - yAmbientPhase * yLeft yAmbientA
def yGraphBEquation : YProductRing := yRight yAmbientB + yAmbientPhase * yLeft yAmbientB
def yDiagonalAEquation : YProductRing := yRight yAmbientA - yLeft yAmbientA
def yDiagonalBEquation : YProductRing := yRight yAmbientB - yLeft yAmbientB
def yGraphIdeal : Ideal YProductRing := RingHom.ker yGraphReceiver
def yDiagonalIdeal : Ideal YProductRing := RingHom.ker yDiagonalReceiver

@[simp] theorem yGraphReceiver_left (a : YChartCubicRing) : yGraphReceiver (yLeft a) = a := by
  simp [yGraphReceiver, yLeft]
@[simp] theorem yGraphReceiver_right (a : YChartCubicRing) : yGraphReceiver (yRight a) = yIotaAlgebraMap a := by
  simp [yGraphReceiver, yRight]
@[simp] theorem yDiagonalReceiver_left (a : YChartCubicRing) : yDiagonalReceiver (yLeft a) = a := by
  simp [yDiagonalReceiver, yLeft]
@[simp] theorem yDiagonalReceiver_right (a : YChartCubicRing) : yDiagonalReceiver (yRight a) = a := by
  simp [yDiagonalReceiver, yRight]
@[simp] theorem yIotaAlgebraMap_a : yIotaAlgebraMap yAmbientA = Complex.I • yAmbientA := by
  change yIotaCoordinateRing (AdjoinRoot.root yMonicCubic) = _
  simpa only [yAmbientA, Algebra.smul_def] using yIotaCoordinateRing_a
@[simp] theorem yIotaAlgebraMap_b : yIotaAlgebraMap yAmbientB = (-Complex.I) • yAmbientB := by
  change yIotaCoordinateRing (AdjoinRoot.of yMonicCubic X) = _
  simpa only [yAmbientB, Algebra.smul_def] using yIotaCoordinateRing_b

theorem yGraphIdeal_eq_two_equations :
    yGraphIdeal = Ideal.span {yGraphAEquation, yGraphBEquation} := by
  let J : Ideal YProductRing := Ideal.span {yGraphAEquation, yGraphBEquation}
  have hle : J ≤ yGraphIdeal := by
    apply Ideal.span_le.mpr
    rintro p (h | h)
    · rw [h]
      change yGraphReceiver yGraphAEquation = 0
      rw [yGraphAEquation, map_sub, map_mul, yGraphReceiver_right, yGraphReceiver_left]
      rw [show yGraphReceiver yAmbientPhase = algebraMap ℂ YChartCubicRing Complex.I from yGraphReceiver.commutes Complex.I]
      simp only [yIotaAlgebraMap_a, Algebra.smul_def, sub_self]
    · rw [Set.mem_singleton_iff.mp h]
      change yGraphReceiver yGraphBEquation = 0
      rw [yGraphBEquation, map_add, map_mul, yGraphReceiver_right, yGraphReceiver_left]
      rw [show yGraphReceiver yAmbientPhase = algebraMap ℂ YChartCubicRing Complex.I from yGraphReceiver.commutes Complex.I]
      simp only [yIotaAlgebraMap_b, Algebra.smul_def, map_neg, neg_mul, neg_add_cancel]
  apply le_antisymm _ hle
  let π : YProductRing →ₐ[ℂ] YProductRing ⧸ J := Ideal.Quotient.mkₐ ℂ J
  have ha : π yGraphAEquation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hb : π yGraphBEquation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hr : π.comp yRight = (π.comp yLeft).comp yIotaAlgebraMap := by
    apply yCoordinateAlgebraMap_ext
    · change π (yRight yAmbientB) = π (yLeft (yIotaAlgebraMap yAmbientB))
      simpa [yGraphBEquation, Algebra.smul_def] using eq_neg_of_add_eq_zero_left hb
    · change π (yRight yAmbientA) = π (yLeft (yIotaAlgebraMap yAmbientA))
      simpa [yGraphAEquation, Algebra.smul_def] using sub_eq_zero.mp ha
  have hwhole : π = (π.comp yLeft).comp yGraphReceiver := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro a; simp [yLeft, yGraphReceiver]
    · apply AlgHom.ext; intro a
      simpa [yRight, yGraphReceiver] using AlgHom.congr_fun hr a
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π p = 0
  rw [hwhole]
  change π (yLeft (yGraphReceiver p)) = 0
  change yGraphReceiver p = 0 at hp
  simp [hp]

theorem yDiagonalIdeal_eq_two_equations :
    yDiagonalIdeal = Ideal.span {yDiagonalAEquation, yDiagonalBEquation} := by
  let J : Ideal YProductRing := Ideal.span {yDiagonalAEquation, yDiagonalBEquation}
  have hle : J ≤ yDiagonalIdeal := by
    apply Ideal.span_le.mpr
    rintro p (h | h)
    · rw [h]; change yDiagonalReceiver yDiagonalAEquation = 0; simp [yDiagonalAEquation]
    · rw [Set.mem_singleton_iff.mp h]
      change yDiagonalReceiver yDiagonalBEquation = 0; simp [yDiagonalBEquation]
  apply le_antisymm _ hle
  let π : YProductRing →ₐ[ℂ] YProductRing ⧸ J := Ideal.Quotient.mkₐ ℂ J
  have ha : π yDiagonalAEquation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hb : π yDiagonalBEquation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hr : π.comp yRight = π.comp yLeft := by
    apply yCoordinateAlgebraMap_ext
    · change π (yRight yAmbientB) = π (yLeft yAmbientB)
      simpa [yDiagonalBEquation] using sub_eq_zero.mp hb
    · change π (yRight yAmbientA) = π (yLeft yAmbientA)
      simpa [yDiagonalAEquation] using sub_eq_zero.mp ha
  have hwhole : π = (π.comp yLeft).comp yDiagonalReceiver := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro a; simp [yLeft, yDiagonalReceiver]
    · apply AlgHom.ext; intro a
      simpa [yRight, yDiagonalReceiver] using AlgHom.congr_fun hr a
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π p = 0
  rw [hwhole]
  change π (yLeft (yDiagonalReceiver p)) = 0
  change yDiagonalReceiver p = 0 at hp
  simp [hp]

def yGraphP : YProductRing := yRight yAmbientA ^ 2 +
  yAmbientPhase * yRight yAmbientA * yLeft yAmbientA - yLeft yAmbientA ^ 2 - yRight yAmbientB ^ 2
def yGraphQ : YProductRing := 1 + yAmbientPhase * yLeft yAmbientA *
  (yRight yAmbientB - yAmbientPhase * yLeft yAmbientB)
def yDiagonalP : YProductRing := yRight yAmbientA ^ 2 +
  yRight yAmbientA * yLeft yAmbientA + yLeft yAmbientA ^ 2 - yRight yAmbientB ^ 2
def yDiagonalQ : YProductRing := 1 + yLeft yAmbientA * (yRight yAmbientB + yLeft yAmbientB)

theorem y_difference_polynomial {R : Type*} [CommRing R] (a b c d : R) :
    (a-c)*(a^2+a*c+c^2-b^2) - (b-d)*(1+c*(b+d)) =
      (a^3-a*b^2-b) - (c^3-c*d^2-d) := by ring

theorem yDiagonal_difference_relation :
    yDiagonalAEquation * yDiagonalP = yDiagonalBEquation * yDiagonalQ := by
  apply sub_eq_zero.mp
  rw [yDiagonalAEquation, yDiagonalBEquation, yDiagonalP, yDiagonalQ, y_difference_polynomial]
  have hL := congrArg yLeft yDerivative_source_relation
  have hR := congrArg yRight yDerivative_source_relation
  simp only [map_sub, map_mul, map_pow, map_zero] at hL hR
  rw [hL, hR, sub_self]

theorem yGraph_difference_relation : yGraphAEquation * yGraphP = yGraphBEquation * yGraphQ := by
  have hc : yAmbientPhase ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hL := congrArg yLeft yDerivative_source_relation
  have hR := congrArg yRight yDerivative_source_relation
  simp only [map_sub, map_mul, map_pow, map_zero] at hL hR
  have hphase : (yAmbientPhase*yLeft yAmbientA)^3 -
      (yAmbientPhase*yLeft yAmbientA)*(-yAmbientPhase*yLeft yAmbientB)^2 -
      (-yAmbientPhase*yLeft yAmbientB) = 0 := by
    calc
      _ = -yAmbientPhase * (yLeft yAmbientA^3 - yLeft yAmbientA*yLeft yAmbientB^2 - yLeft yAmbientB) := by
        ring_nf
        rw [show yAmbientPhase ^ 3 = -yAmbientPhase by rw [pow_succ, hc]; ring]
        ring
      _ = 0 := by rw [hL, mul_zero]
  have he := y_difference_polynomial (yRight yAmbientA) (yRight yAmbientB)
    (yAmbientPhase*yLeft yAmbientA) (-yAmbientPhase*yLeft yAmbientB)
  rw [hR, hphase, sub_self] at he
  apply sub_eq_zero.mp
  convert he using 1 <;> unfold yGraphAEquation yGraphBEquation yGraphP yGraphQ <;>
    simp only [mul_pow, hc] <;> ring

#print axioms yGraphIdeal_eq_two_equations
#print axioms yDiagonalIdeal_eq_two_equations
#print axioms yDiagonal_difference_relation
#print axioms yGraph_difference_relation
end Holonics.Hodge.CMGraphSource
