import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Joint pair balls and normalized receiving combinations

These are finite-dimensional norm laws for the normalized pair current.  They retain the joint
weighted centre and a single value-ball radius; they do not assert a nonlinear compression or an
optimization improvement.
-/

open scoped BigOperators Real RealInnerProductSpace

namespace Holonics.Transport.PairJointBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem partition_unity_anchor
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (v : ι → E) (v₀ : E)
    (hp : ∑ i, p i = 1) :
    (∑ i, p i • v i) = v₀ + ∑ i, p i • (v i - v₀) := by
  simp only [sub_eq_add_neg, smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, hp, one_smul]
  abel

theorem simplex_weighted_deviation_bound
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (dv : ι → E) {r : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hdv : ∀ i, ‖dv i‖ ≤ r) :
    ‖∑ i, p i • dv i‖ ≤ r := by
  calc
    ‖∑ i, p i • dv i‖ ≤ ∑ i, ‖p i • dv i‖ := norm_sum_le (s := Finset.univ) _
    _ ≤ ∑ i, p i * r := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp i)]
      exact mul_le_mul_of_nonneg_left (hdv i) (hp i)
    _ = r := by
      rw [← Finset.sum_mul, hsum, one_mul]

theorem scalar_vector_perturbation_bound
    (b db : ℝ) (x dx : E) {rB rX : ℝ}
    (hdb : |db| ≤ rB) (hdx : ‖dx‖ ≤ rX) :
    ‖(b + db) • (x + dx) - b • x‖ ≤
      |b| * rX + rB * (‖x‖ + rX) := by
  have hrB : 0 ≤ rB := le_trans (abs_nonneg db) hdb
  have hbdx : ‖b • dx‖ ≤ |b| * rX := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hdx (abs_nonneg b)
  have hdbx : ‖db • x‖ ≤ rB * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hdb (norm_nonneg x)
  have hdbdx : ‖db • dx‖ ≤ rB * rX := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |db| * ‖dx‖ ≤ rB * ‖dx‖ := mul_le_mul_of_nonneg_right hdb (norm_nonneg dx)
      _ ≤ rB * rX := mul_le_mul_of_nonneg_left hdx hrB
  calc
    ‖(b + db) • (x + dx) - b • x‖ = ‖b • dx + db • x + db • dx‖ := by
      congr 1
      simp only [smul_add, add_smul, sub_eq_add_neg]
      abel
    _ ≤ ‖b • dx‖ + ‖db • x‖ + ‖db • dx‖ := norm_add₃_le
    _ ≤ |b| * rX + rB * (‖x‖ + rX) := by
      nlinarith [hbdx, hdbx, hdbdx]

section Inner

variable [InnerProductSpace ℝ E]

omit [NormedSpace ℝ E] in
def realPair (x y : E) : ℝ := inner ℝ x y

omit [NormedSpace ℝ E] in
theorem inner_product_perturbation_bound
    (g dg v dv : E) {rG rV : ℝ}
    (hdg : ‖dg‖ ≤ rG) (hdv : ‖dv‖ ≤ rV) :
    ‖realPair (g + dg) (v + dv) - realPair g v‖ ≤
      ‖g‖ * rV + ‖v‖ * rG + rG * rV := by
  have hGv : ‖realPair g dv‖ ≤ ‖g‖ * rV := by
    simp only [realPair]
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm g dv).trans
      (mul_le_mul_of_nonneg_left hdv (norm_nonneg g))
  have hdvG : ‖realPair dg v‖ ≤ ‖v‖ * rG := by
    simp only [realPair]
    rw [Real.norm_eq_abs, real_inner_comm]
    exact (abs_real_inner_le_norm v dg).trans
      (mul_le_mul_of_nonneg_left hdg (norm_nonneg v))
  have hdvdv : ‖realPair dg dv‖ ≤ rG * rV := by
    simp only [realPair]
    rw [Real.norm_eq_abs]
    calc
      |inner ℝ dg dv| ≤ ‖dg‖ * ‖dv‖ := abs_real_inner_le_norm dg dv
      _ ≤ rG * ‖dv‖ := mul_le_mul_of_nonneg_right hdg (norm_nonneg dv)
      _ ≤ rG * rV := mul_le_mul_of_nonneg_left hdv (le_trans (norm_nonneg dg) hdg)
  calc
    ‖realPair (g + dg) (v + dv) - realPair g v‖ =
        ‖realPair g dv + realPair dg v + realPair dg dv‖ := by
          congr 1
          simp only [realPair, inner_add_left, inner_add_right, sub_eq_add_neg]
          abel
    _ ≤ ‖realPair g dv‖ + ‖realPair dg v‖ + ‖realPair dg dv‖ := norm_add₃_le
    _ ≤ ‖g‖ * rV + ‖v‖ * rG + rG * rV := by
      nlinarith [hGv, hdvG, hdvdv]

end Inner

end Holonics.Transport.PairJointBall
