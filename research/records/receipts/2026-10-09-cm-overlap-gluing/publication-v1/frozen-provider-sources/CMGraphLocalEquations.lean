import CMGraphAffine
import Mathlib.RingTheory.Localization.Away.Basic

/-!
The genuine tensor-product affine graph ideal has two explicit equations.
Their difference-of-cubic relation provides two local principal equations.
The two denominator faces cover the graph via an exact Bezout identity.
Regularity of these generators in the surface local rings, and the join
to the projective graph's opens, remain necessary for a Cartier claim.
-/
noncomputable section
open scoped TensorProduct
namespace Holonics.Hodge.CMGraphSource

def graphLeft : CurveRing →ₐ[ℂ] ProductRing := Algebra.TensorProduct.includeLeft
def graphRight : CurveRing →ₐ[ℂ] ProductRing := Algebra.TensorProduct.includeRight
def graphXEquation : ProductRing := graphRight u + graphLeft u
def graphVEquation : ProductRing := graphRight v - Complex.I • graphLeft v
def graphTwoEquationIdeal : Ideal ProductRing := Ideal.span {graphXEquation, graphVEquation}

@[simp] theorem graphReceiver_left (a : CurveRing) : graphReceiver (graphLeft a) = a := by
  simp [graphReceiver, graphLeft]
@[simp] theorem graphReceiver_right (a : CurveRing) : graphReceiver (graphRight a) = iota a := by
  simp [graphReceiver, graphRight]

theorem graphTwoEquationIdeal_le : graphTwoEquationIdeal ≤ graphIdeal := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · change graphReceiver graphXEquation = 0
    simp [graphXEquation, iota]
  · rcases Set.mem_singleton_iff.mp hp with rfl
    change graphReceiver graphVEquation = 0
    simp [graphVEquation, iota]

theorem graphIdeal_eq_two_equations : graphIdeal = graphTwoEquationIdeal := by
  apply le_antisymm _ graphTwoEquationIdeal_le
  let π : ProductRing →ₐ[ℂ] ProductRing ⧸ graphTwoEquationIdeal :=
    Ideal.Quotient.mkₐ ℂ graphTwoEquationIdeal
  have hx : π graphXEquation = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hv : π graphVEquation = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hright : π.comp graphRight = (π.comp graphLeft).comp iota := by
    apply curveRing_hom_ext
    · change π (graphRight u) = π (graphLeft (iota u))
      simpa [graphXEquation, iota] using eq_neg_of_add_eq_zero_left hx
    · change π (graphRight v) = π (graphLeft (iota v))
      simpa [graphVEquation, iota] using sub_eq_zero.mp hv
  have hwhole : π = (π.comp graphLeft).comp graphReceiver := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro a
      simp [graphLeft, graphReceiver]
    · apply AlgHom.ext
      intro a
      simpa [graphRight, graphReceiver] using AlgHom.congr_fun hright a
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π p = 0
  rw [hwhole]
  change π (graphLeft (graphReceiver p)) = 0
  change graphReceiver p = 0 at hp
  simp [hp]

def graphCubicFactor : ProductRing :=
  graphRight u ^ 2 - graphRight u * graphLeft u + graphLeft u ^ 2 - 1
def graphVSum : ProductRing := graphRight v + Complex.I • graphLeft v

theorem graph_difference_relation :
    graphXEquation * graphCubicFactor = graphVEquation * graphVSum := by
  have hL : graphLeft v ^ 2 = graphLeft u ^ 3 - graphLeft u := by
    rw [← map_pow, curve_relation, map_sub, map_pow]
  have hR : graphRight v ^ 2 = graphRight u ^ 3 - graphRight u := by
    rw [← map_pow, curve_relation, map_sub, map_pow]
  have hI : (Complex.I • graphLeft v) ^ 2 = -(graphLeft v ^ 2) := by
    rw [smul_pow, Complex.I_sq, neg_one_smul]
  calc
    _ = graphRight v ^ 2 + graphLeft v ^ 2 := by
      rw [hL, hR]
      unfold graphXEquation graphCubicFactor
      ring
    _ = graphVEquation * graphVSum := by
      unfold graphVEquation graphVSum
      calc
        _ = graphRight v ^ 2 - (Complex.I • graphLeft v) ^ 2 := by rw [hI]; ring
        _ = _ := by ring

@[simp] theorem graphReceiver_factor :
    graphReceiver graphCubicFactor = 3 * u ^ 2 - 1 := by
  simp [graphCubicFactor, iota]
  ring
@[simp] theorem graphReceiver_vsum : graphReceiver graphVSum = (2 * Complex.I) • v := by
  simp [graphVSum, iota]
  module

theorem graph_principal_faces_cover :
    Ideal.span ({graphReceiver graphCubicFactor, graphReceiver graphVSum} : Set CurveRing) = ⊤ := by
  let J : Ideal CurveRing := Ideal.span {graphReceiver graphCubicFactor, graphReceiver graphVSum}
  have hc : 3 * u ^ 2 - 1 ∈ J := by
    rw [← graphReceiver_factor]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hw : (2 * Complex.I) • v ∈ J := by
    rw [← graphReceiver_vsum]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hv : v ∈ J := by
    have hm := J.mul_mem_left (algebraMap ℂ CurveRing ((2 * Complex.I : ℂ)⁻¹)) hw
    rw [← Algebra.smul_def] at hm
    have hn : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hm
  have hbez : (3 * u ^ 2 - 1) * (3 * u ^ 2 - 2) - 9 * (u * v * v) = 2 := by
    rw [show u * v * v = u * v ^ 2 by ring, curve_relation]
    ring
  have htwo : (2 : CurveRing) ∈ J := hbez ▸ J.sub_mem
    (J.mul_mem_right (3 * u ^ 2 - 2) hc)
    (J.mul_mem_left 9 (J.mul_mem_right v (J.mul_mem_left u hv)))
  have hunit : IsUnit (2 : CurveRing) := by
    have h := IsUnit.map (algebraMap ℂ CurveRing) (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0))
    simpa only [map_ofNat] using h
  exact Ideal.eq_top_of_isUnit_mem J htwo hunit

#print axioms graphIdeal_eq_two_equations
#print axioms graph_difference_relation
#print axioms graph_principal_faces_cover
end Holonics.Hodge.CMGraphSource
