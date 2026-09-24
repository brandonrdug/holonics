import Mathlib

/-!
# Positive bilateral Laplace weights and reflection permit off-line zeros

The three positive source masses at logarithmic addresses 0 and ±1 give
F(s)=1+(6/13)(exp(s-1/2)+exp(-(s-1/2))). This entire source is invariant
under s ↦ 1-s, but it vanishes at 1/2+log(3/2)+iπ, strictly inside the
open critical strip and off its fixed line. Thus positivity of the
source weights, evenness and a reflected phase current do not by themselves
give the Weil-square positivity of the actual xi divisor.
-/

noncomputable section

namespace Holonics.RH.PositiveLaplaceOffLineControl

open Complex

def positiveEvenLaplace (s : ℂ) : ℂ :=
  1 + (6 / 13 : ℂ) *
    (Complex.exp (s - 1 / 2) + Complex.exp (-(s - 1 / 2)))

theorem positiveEvenLaplace_reflection (s : ℂ) :
    positiveEvenLaplace (1 - s) = positiveEvenLaplace s := by
  have h : (1 - s) - (1 / 2 : ℂ) = -(s - 1 / 2) := by ring
  simp only [positiveEvenLaplace, h, neg_neg]
  ring

theorem positiveEvenLaplace_differentiable :
    Differentiable ℂ positiveEvenLaplace := by
  unfold positiveEvenLaplace
  fun_prop

def offLinePoint : ℂ :=
  1 / 2 + (Real.log (3 / 2) : ℂ) + (Real.pi : ℂ) * Complex.I

private theorem exp_target :
    Complex.exp ((Real.log (3 / 2) : ℂ) + (Real.pi : ℂ) * Complex.I) = -3 / 2 := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by norm_num),
    Complex.exp_pi_mul_I]
  norm_num

theorem positiveEvenLaplace_offLine_zero :
    positiveEvenLaplace offLinePoint = 0 := by
  have hw : offLinePoint - (1 / 2 : ℂ) =
      (Real.log (3 / 2) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    unfold offLinePoint
    ring
  unfold positiveEvenLaplace
  rw [hw, exp_target, Complex.exp_neg, exp_target]
  norm_num

theorem offLinePoint_real_ne_half :
    offLinePoint.re ≠ 1 / 2 := by
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hre : offLinePoint.re = 1 / 2 + Real.log (3 / 2) := by
    simp [offLinePoint, Complex.add_re, Complex.mul_re]
  rw [hre]
  linarith

theorem offLinePoint_in_strip :
    0 < offLinePoint.re ∧ offLinePoint.re < 1 := by
  have hpos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hsmall : Real.log (3 / 2) < 1 / 2 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 3 / 2 by norm_num) (by norm_num : (3 / 2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  have hre : offLinePoint.re = 1 / 2 + Real.log (3 / 2) := by
    simp [offLinePoint, Complex.add_re, Complex.mul_re]
  rw [hre]
  constructor <;> linarith

end Holonics.RH.PositiveLaplaceOffLineControl

section Audit
open Holonics.RH.PositiveLaplaceOffLineControl
#print axioms positiveEvenLaplace_reflection
#print axioms positiveEvenLaplace_differentiable
#print axioms positiveEvenLaplace_offLine_zero
#print axioms offLinePoint_real_ne_half
#print axioms offLinePoint_in_strip
end Audit
