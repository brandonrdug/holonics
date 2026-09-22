import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Joint Euclidean balls for an affine current chart

This owner gives the generic norm budget used by the native affine current map.  The coefficient
ball is joint: the linear map, the real translation and the input perturbation are bounded in
their declared norms.  The result is a forward/adjoint enclosure estimate; it does not claim that
the native kernel computes the operator norm bound or that a proposal improves an objective.
-/

open scoped Real

namespace Soma.Holonics.Transport.AffineJointBall

variable {E F G : Type*}

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affine_forward_deviation
    (R dR : E →L[ℝ] F) (x dx : E) (t dt : F)
    {K rM rX : ℝ}
    (hR : ‖R‖ ≤ K) (hdR : ‖dR‖ ≤ rM) (hdt : ‖dt‖ ≤ rM) (hdx : ‖dx‖ ≤ rX) :
    ‖(R + dR) (x + dx) + (t + dt) - (R x + t)‖ ≤
      K * rX + rM * (‖x‖ + rX + 1) := by
  have hK : 0 ≤ K := le_trans (norm_nonneg R) hR
  have hrM : 0 ≤ rM := le_trans (norm_nonneg dR) hdR
  have hRdx : ‖R dx‖ ≤ K * rX := by
    calc
      ‖R dx‖ ≤ ‖R‖ * ‖dx‖ := R.le_opNorm dx
      _ ≤ K * ‖dx‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg dx)
      _ ≤ K * rX := mul_le_mul_of_nonneg_left hdx hK
  have hdRx : ‖dR x‖ ≤ rM * ‖x‖ :=
    (dR.le_opNorm x).trans (mul_le_mul_of_nonneg_right hdR (norm_nonneg x))
  have hdRdx : ‖dR dx‖ ≤ rM * rX := by
    calc
      ‖dR dx‖ ≤ ‖dR‖ * ‖dx‖ := dR.le_opNorm dx
      _ ≤ rM * ‖dx‖ := mul_le_mul_of_nonneg_right hdR (norm_nonneg dx)
      _ ≤ rM * rX := mul_le_mul_of_nonneg_left hdx hrM
  calc
    ‖(R + dR) (x + dx) + (t + dt) - (R x + t)‖
        = ‖R dx + dR x + dR dx + dt‖ := by
          congr 1
          simp only [map_add, add_apply, sub_eq_add_neg]
          abel
    _ ≤ ‖R dx‖ + ‖dR x‖ + ‖dR dx‖ + ‖dt‖ := by
          exact norm_add₄_le
    _ ≤ K * rX + rM * (‖x‖ + rX + 1) := by
          nlinarith [hRdx, hdRx, hdRdx, hdt]

theorem affine_forward_with_arithmetic_radius
    (R dR : E →L[ℝ] F) (x dx : E) (t dt rounded : F)
    {K rM rX rA : ℝ}
    (hR : ‖R‖ ≤ K) (hdR : ‖dR‖ ≤ rM) (hdt : ‖dt‖ ≤ rM) (hdx : ‖dx‖ ≤ rX)
    (hA : ‖(R x + t) - rounded‖ ≤ rA) :
    ‖(R + dR) (x + dx) + (t + dt) - rounded‖ ≤
      K * rX + rM * (‖x‖ + rX + 1) + rA := by
  have h := affine_forward_deviation R dR x dx t dt hR hdR hdt hdx
  calc
    _ = ‖((R + dR) (x + dx) + (t + dt) - (R x + t)) +
          ((R x + t) - rounded)‖ := by congr 1; abel
    _ ≤ ‖(R + dR) (x + dx) + (t + dt) - (R x + t)‖ +
          ‖(R x + t) - rounded‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h hA

theorem projection_nonexpansive
    (P : F →L[ℝ] F) {y z : F} (hP : ‖P‖ ≤ 1) :
    ‖P y - P z‖ ≤ ‖y - z‖ := by
  rw [← map_sub]
  calc
    ‖P (y - z)‖ ≤ ‖P‖ * ‖y - z‖ := P.le_opNorm _
    _ ≤ ‖y - z‖ := by nlinarith [norm_nonneg (y - z)]

theorem exact_identity_ball_no_inflation
    (x dx : E) {rX : ℝ} (hdx : ‖dx‖ ≤ rX) :
    ‖(ContinuousLinearMap.id ℝ E) (x + dx) - (ContinuousLinearMap.id ℝ E) x‖ ≤ rX := by
  convert hdx using 1 <;> simp only [ContinuousLinearMap.id_apply] <;> abel

end Normed

section AdjointChart

variable [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/- The adjoint chart is supplied by the caller.  This keeps the theorem valid for the native
identity-metric pullback without silently asserting an inner-product adjoint or a matrix norm
formula. -/
theorem adjoint_deviation
    (A dA : F →L[ℝ] G) (g dg : F)
    {K rM rG : ℝ}
    (hA : ‖A‖ ≤ K) (hdA : ‖dA‖ ≤ rM) (hdg : ‖dg‖ ≤ rG) :
    ‖(A + dA) (g + dg) - A g‖ ≤
      K * rG + rM * (‖g‖ + rG) := by
  have hK : 0 ≤ K := le_trans (norm_nonneg A) hA
  have hrM : 0 ≤ rM := le_trans (norm_nonneg dA) hdA
  have hAdg : ‖A dg‖ ≤ K * rG := by
    calc
      ‖A dg‖ ≤ ‖A‖ * ‖dg‖ := A.le_opNorm dg
      _ ≤ K * ‖dg‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg dg)
      _ ≤ K * rG := mul_le_mul_of_nonneg_left hdg hK
  have hdAg : ‖dA g‖ ≤ rM * ‖g‖ :=
    (dA.le_opNorm g).trans (mul_le_mul_of_nonneg_right hdA (norm_nonneg g))
  have hdAdg : ‖dA dg‖ ≤ rM * rG := by
    calc
      ‖dA dg‖ ≤ ‖dA‖ * ‖dg‖ := dA.le_opNorm dg
      _ ≤ rM * ‖dg‖ := mul_le_mul_of_nonneg_right hdA (norm_nonneg dg)
      _ ≤ rM * rG := mul_le_mul_of_nonneg_left hdg hrM
  calc
    ‖(A + dA) (g + dg) - A g‖ = ‖A dg + dA g + dA dg‖ := by
      congr 1
      simp only [map_add, add_apply, sub_eq_add_neg]
      abel
    _ ≤ ‖A dg‖ + ‖dA g‖ + ‖dA dg‖ := norm_add₃_le
    _ ≤ K * rG + rM * (‖g‖ + rG) := by
      nlinarith [hAdg, hdAg, hdAdg]

end AdjointChart

end Soma.Holonics.Transport.AffineJointBall
