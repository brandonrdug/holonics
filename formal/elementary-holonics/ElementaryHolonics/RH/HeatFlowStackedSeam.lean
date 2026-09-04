import Mathlib
import ElementaryHolonics.RH.HeatFlowOfPolynomials

/-!
# The stacked seam unfolds into the Hermite optimum, and the kernel's length is the rotation
constant

Three exact clauses of one compound statement about the backward heat flow `heat t p = e^{−tD²} p`:

* **chaining** (`e`): the flow commutes past multiplication by `X` at the cost of one derivative,
  `heat t (X · p) = X · heat t p − 2t · (heat t p)′`, the polynomial face of
  `e^{−tD²} X e^{tD²} = X − 2tD`; with the semigroup law of `HeatSemigroup` this is the whole
  chaining content of the flow;
* **the stacked seam**: at time one half the monomial `X^n`, an `n`-fold zero at the origin,
  becomes the probabilists' Hermite polynomial, `heat (1/2) (X^n) = He_n`, whose zeros are
  Stieltjes' electrostatic equilibrium of the confined log-gas; a maximally degenerate seam
  unfolds along its threads into the optimum; and
* **rotation** (`π`): the length of the forward heat kernel is the Gaussian integral,
  `∫ e^{−z²/(4t)} dz = √(4πt)`, the rotation constant, so the kernel's normalization is
  `(4πt)^{−1/2}`.

The reading is in the dated record of 2026-09-03; every theorem here is discharged with no
`sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.HeatFlowStackedSeam

open Polynomial Finset Soma.Holonics.RH.HeatFlowOfPolynomials

/-- The iterated derivative of `X · p`: one factor of `X` survives, and each derivative that
lands on the `X` leaves one fewer derivative on `p`. -/
theorem iterate_derivative_X_mul (p : ℂ[X]) (m : ℕ) :
    derivative^[m + 1] (X * p) =
      X * derivative^[m + 1] p + ((m + 1 : ℕ) : ℂ[X]) * derivative^[m] p := by
  induction m with
  | zero =>
    simp [derivative_mul]
    ring
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, derivative_add, derivative_mul, derivative_X,
      derivative_mul, derivative_natCast, ← Function.iterate_succ_apply' derivative (m + 1),
      ← Function.iterate_succ_apply' derivative m]
    push_cast
    ring

/-- `heat` may be summed over any range past the degree, since higher derivatives vanish. -/
theorem heat_eq_sum_of_le {p : ℂ[X]} {m : ℕ} (hm : p.natDegree ≤ m) (t : ℝ) :
    heat t p = ∑ k ∈ range (m + 1),
      C (((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) * (derivative^[2 * k] p) := by
  unfold heat
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    have hdeg : p.natDegree < 2 * k := by omega
    rw [iterate_derivative_eq_zero hdeg, mul_zero]

/-- **Chaining past `X`**: `heat t (X · p) = X · heat t p − 2t · (heat t p)′`. -/
theorem heat_X_mul (t : ℝ) (p : ℂ[X]) :
    heat t (X * p) = X * heat t p - C ((2 * t : ℝ) : ℂ) * derivative (heat t p) := by
  have hdeg : (X * p).natDegree ≤ p.natDegree + 1 := by
    calc (X * p).natDegree ≤ X.natDegree + p.natDegree := natDegree_mul_le
      _ ≤ p.natDegree + 1 := by rw [natDegree_X]; omega
  rw [derivative_heat, heat_eq_sum_of_le hdeg, heat_eq_sum_of_le (Nat.le_succ p.natDegree)]
  rw [Finset.sum_range_succ' (fun k => C (((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) *
    derivative^[2 * k] (X * p))]
  simp only [Nat.factorial_zero, pow_zero, Nat.cast_one, div_one, map_one, one_mul,
    Function.iterate_zero, id_eq, mul_zero]
  have hterm : ∀ j : ℕ, C (((-t : ℝ) : ℂ) ^ (j + 1) / ((j + 1).factorial : ℂ)) *
      derivative^[2 * (j + 1)] (X * p) =
      X * (C (((-t : ℝ) : ℂ) ^ (j + 1) / ((j + 1).factorial : ℂ)) * derivative^[2 * (j + 1)] p)
      - C ((2 * t : ℝ) : ℂ) *
        (C (((-t : ℝ) : ℂ) ^ j / (j.factorial : ℂ)) * derivative^[2 * j + 1] p) := by
    intro j
    have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [h2, iterate_derivative_X_mul]
    have hfac : (((2 * j + 1 + 1 : ℕ) : ℂ[X])) *
        C (((-t : ℝ) : ℂ) ^ (j + 1) / ((j + 1).factorial : ℂ)) =
        - C ((2 * t : ℝ) : ℂ) * C (((-t : ℝ) : ℂ) ^ j / (j.factorial : ℂ)) := by
      rw [← C_eq_natCast, ← C_mul, neg_mul, ← C_mul, ← C_neg]
      congr 1
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    calc C (((-t : ℝ) : ℂ) ^ (j + 1) / ((j + 1).factorial : ℂ)) *
          (X * derivative^[2 * j + 1 + 1] p +
            ((2 * j + 1 + 1 : ℕ) : ℂ[X]) * derivative^[2 * j + 1] p)
        = X * (C (((-t : ℝ) : ℂ) ^ (j + 1) / ((j + 1).factorial : ℂ)) *
            derivative^[2 * j + 1 + 1] p) +
          (((2 * j + 1 + 1 : ℕ) : ℂ[X]) * C (((-t : ℝ) : ℂ) ^ (j + 1) / ((j + 1).factorial : ℂ)))
            * derivative^[2 * j + 1] p := by ring
      _ = _ := by
          rw [hfac]
          have h3 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
          rw [h3]
          ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_range_succ' (fun k => C (((-t : ℝ) : ℂ) ^ k /
      (k.factorial : ℂ)) * derivative^[2 * k] p)]
  simp only [Nat.factorial_zero, pow_zero, Nat.cast_one, div_one, map_one, one_mul,
    Function.iterate_zero, id_eq, mul_zero]
  ring

/-- The probabilists' Hermite polynomial over `ℂ`. -/
def hermiteC (n : ℕ) : ℂ[X] := (Polynomial.hermite n).map (Int.castRingHom ℂ)

theorem hermiteC_zero : hermiteC 0 = 1 := by
  simp [hermiteC, Polynomial.hermite_zero]

theorem hermiteC_succ (n : ℕ) :
    hermiteC (n + 1) = X * hermiteC n - derivative (hermiteC n) := by
  simp only [hermiteC, Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, derivative_map]

/-- **The stacked seam unfolds into the Hermite optimum**: `heat (1/2) (X^n) = He_n`. -/
theorem heat_half_X_pow (n : ℕ) : heat (1 / 2 : ℝ) (X ^ n) = hermiteC n := by
  induction n with
  | zero =>
    rw [pow_zero, hermiteC_zero]
    unfold heat
    simp
  | succ n ih =>
    rw [pow_succ', heat_X_mul, ih, hermiteC_succ]
    have h : ((2 * (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by norm_num
    rw [h, map_one, one_mul]

/-- **The kernel's length is the rotation constant**: `∫ e^{−z²/(4t)} dz = √(4πt)` for `t > 0`. -/
theorem integral_heat_kernel {t : ℝ} (ht : 0 < t) :
    ∫ z : ℝ, Real.exp (-(z ^ 2) / (4 * t)) = Real.sqrt (4 * Real.pi * t) := by
  have hb : 0 < 1 / (4 * t) := by positivity
  have h := integral_gaussian (1 / (4 * t))
  have hfun : (fun z : ℝ => Real.exp (-(1 / (4 * t)) * z ^ 2)) =
      fun z : ℝ => Real.exp (-(z ^ 2) / (4 * t)) := by
    funext z
    congr 1
    ring
  have harg : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
    rw [div_div_eq_mul_div, div_one]
    ring
  rw [hfun] at h
  rw [h, harg]

end Soma.Holonics.RH.HeatFlowStackedSeam
