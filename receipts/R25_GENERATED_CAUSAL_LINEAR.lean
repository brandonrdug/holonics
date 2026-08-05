import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Soma.Holonics.R25

theorem generated_causal_linear_calculus :
  (5 + 1 = 6 ∧ 5 + 1 = 6 ∧ 2 = 2 ∧ 15 + 1 = 16 ∧ 25 = 25 ∧ (1 : ℤ) = 1 ∧ (1 : ℤ) = 1 ∧ 2 ≠ 1) ∧
  (∀ x : ℤ, (((x - (-3))^5 * (x - (1))^10 * (x - (5))^1) = (1*x^16 + 0*x^15 + -40*x^14 + 0*x^13 + 540*x^12 + -384*x^11 + -3480*x^10 + 5760*x^9 + 8070*x^8 + -29440*x^7 + 17640*x^6 + 37120*x^5 + -82020*x^4 + 74880*x^3 + -37800*x^2 + 10368*x^1 + -1215*x^0))) ∧
  (∀ t : ℤ, ((0 + 1*t) * (0 + -1*t) - ((-1 + 0*t) * (0 + 1*t)) = (0 + 1*t + -1*t^2))) ∧
  (∀ q : ℚ, q^2 + 1 ≠ 0) ∧
  (((1*0*1 + 1*1*0 + 0*-1*1 + 0*0*0 : ℤ) = 0) ∧ ((1*0*2 + 1*1*1 + 0*-1*2 + 0*0*1 : ℤ) = 1) ∧ ((2*0*1 + 2*1*0 + 1*-1*1 + 1*0*0 : ℤ) = -1) ∧ ((2*0*2 + 2*1*1 + 1*-1*2 + 1*0*1 : ℤ) = 0) ∧ ((1*0*1 + 1*1*-2 + -2*-1*1 + -2*0*-2 : ℤ) = 0) ∧ ((1*0*0 + 1*1*1 + -2*-1*0 + -2*0*1 : ℤ) = 1) ∧ ((0*0*1 + 0*1*-2 + 1*-1*1 + 1*0*-2 : ℤ) = -1) ∧ ((0*0*0 + 0*1*1 + 1*-1*0 + 1*0*1 : ℤ) = 0) ∧ ((1*0*1 + 1*1*2 + 2*-1*1 + 2*0*2 : ℤ) = 0) ∧ ((1*0*-2 + 1*1*-3 + 2*-1*-2 + 2*0*-3 : ℤ) = 1) ∧ ((-2*0*1 + -2*1*2 + -3*-1*1 + -3*0*2 : ℤ) = -1) ∧ ((-2*0*-2 + -2*1*-3 + -3*-1*-2 + -3*0*-3 : ℤ) = 0))
 := by
  constructor
  · norm_num
  constructor
  · intro x; ring
  constructor
  · intro t; ring
  constructor
  · intro q; nlinarith [sq_nonneg q]
  · norm_num

end Soma.Holonics.R25

#check Soma.Holonics.R25.generated_causal_linear_calculus
