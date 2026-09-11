import Mathlib

/-!
# Machin's exact phase constraint

This source records the lifted real identity behind Machin's formula together
with its exact Gaussian integer arithmetic.  The equalities are algebraic
phase data; they do not introduce a numerical approximation or a convergence
claim for any iteration.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.MachinPhaseConstraint

theorem machin_lifted_pi :
    Real.pi = 16 * Real.arctan (1 / 5 : ℝ) - 4 * Real.arctan (1 / 239 : ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [one_div] at h ⊢
  linarith

theorem gaussian_machin_factorization :
    ((5 : ℂ) + Complex.I) ^ 4 = ((239 : ℂ) + Complex.I) * (2 + 2 * Complex.I) := by
  apply Complex.ext <;> norm_num [pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]

end Soma.Holonics.Mathematics.MachinPhaseConstraint
