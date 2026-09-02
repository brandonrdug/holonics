import ElementaryHolonics.RH.EntireDerivativeGrowth
import ElementaryHolonics.RH.HeatFlowOfPolynomials
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The derivative-series heat flow as an entire function

`heatE t f z = Σ_k (−t)^k/k! · f^{(2k)}(z)`.  On a polynomial it is the polynomial flow `heat`.
For an entire `f` of order below two the terms are bounded on every ball by a summable majorant
independent of the point, so `heatE t f` is entire.
-/

open Complex Metric Filter Topology Finset Polynomial
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowOfPolynomials

namespace Soma.Holonics.RH.HeatFlowEntire

/-- The derivative-series heat flow. -/
noncomputable def heatE (t : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ := ∑' k, heatTerm t f z k

theorem iteratedDeriv_eval (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun z => p.eval z) = fun z => (derivative^[n] p).eval z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [Function.iterate_succ_apply', Polynomial.deriv]

theorem heatTerm_poly (t : ℝ) (p : ℂ[X]) (z : ℂ) (k : ℕ) :
    heatTerm t (fun w => p.eval w) z k =
      (((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) * (derivative^[2 * k] p).eval z := by
  unfold heatTerm
  rw [iteratedDeriv_eval, Complex.ofReal_neg]

theorem heatTerm_poly_eq_zero (t : ℝ) (p : ℂ[X]) (z : ℂ) {k : ℕ} (hk : p.natDegree < k) :
    heatTerm t (fun w => p.eval w) z k = 0 := by
  rw [heatTerm_poly, iterate_derivative_eq_zero (by omega : p.natDegree < 2 * k), eval_zero,
    mul_zero]

/-- On polynomials the derivative series is the polynomial flow. -/
theorem heatE_poly (t : ℝ) (p : ℂ[X]) (z : ℂ) :
    heatE t (fun w => p.eval w) z = (heat t p).eval z := by
  unfold heatE heat
  rw [tsum_eq_sum (s := range (p.natDegree + 1)), eval_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [heatTerm_poly, eval_mul, eval_C]
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    exact heatTerm_poly_eq_zero t p z (by omega)

/-- The term `k = 0` is `f` itself. -/
theorem heatTerm_zero (t : ℝ) (f : ℂ → ℂ) (z : ℂ) : heatTerm t f z 0 = f z := by
  unfold heatTerm
  simp

/-- The geometric-type majorant `v k = (C k^{−δ})^k` for `k ≥ 1`, `v 0 = 1`. -/
noncomputable def majorant (C δ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else (C * (k : ℝ) ^ (-δ)) ^ k

theorem summable_majorant {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) : Summable (majorant C δ) := by
  have hlim : Tendsto (fun k : ℕ => C * (k : ℝ) ^ (-δ)) atTop (𝓝 (C * 0)) :=
    ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul C
  rw [mul_zero] at hlim
  have hev : ∀ᶠ k : ℕ in atTop, ‖majorant C δ k‖ ≤ (1 / 2 : ℝ) ^ k := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_gt_atTop 0] with k hk hk0
    have h0 : 0 ≤ C * (k : ℝ) ^ (-δ) := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    rw [majorant, if_neg hk0.ne', Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 k)]
    exact pow_le_pow_left₀ h0 hk.le k
  exact Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) hev

variable {f : ℂ → ℂ} {A B ρ : ℝ}

/-- On the ball of radius `r` every term is bounded by the majorant times a constant. -/
theorem norm_heatTerm_le_majorant (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (t : ℝ) {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : ‖z‖ ≤ r) (k : ℕ) :
    ‖heatTerm t f z k‖ ≤ (A * Real.exp (B * 2 ^ ρ * r ^ ρ)) *
      majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) k := by
  have h2ρ : (1 : ℝ) ≤ 2 ^ ρ := Real.one_le_rpow (by norm_num) hρ0.le
  have hzr : ‖z‖ ^ ρ ≤ r ^ ρ := Real.rpow_le_rpow (norm_nonneg _) hz hρ0.le
  have hrρ : 0 ≤ r ^ ρ := Real.rpow_nonneg hr _
  have hM : B * 2 ^ ρ * ‖z‖ ^ ρ ≤ B * 2 ^ ρ * r ^ ρ := by
    apply mul_le_mul_of_nonneg_left hzr
    exact mul_nonneg hB (by linarith)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [heatTerm_zero, majorant, if_pos rfl, mul_one]
    refine (hg z).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    have hzρ : 0 ≤ ‖z‖ ^ ρ := Real.rpow_nonneg (norm_nonneg z) ρ
    calc B * ‖z‖ ^ ρ = B * ‖z‖ ^ ρ * 1 := by ring
      _ ≤ B * ‖z‖ ^ ρ * 2 ^ ρ := mul_le_mul_of_nonneg_left h2ρ (mul_nonneg hB hzρ)
      _ = B * 2 ^ ρ * ‖z‖ ^ ρ := by ring
      _ ≤ B * 2 ^ ρ * r ^ ρ := hM
  · rw [majorant, if_neg hk.ne']
    refine (norm_heatTerm_le hf hg hA hB hρ0 t z hk).trans ?_
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)) k)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hM) hA

theorem differentiable_heatTerm (hf : Differentiable ℂ f) (t : ℝ) (k : ℕ) :
    Differentiable ℂ (fun z => heatTerm t f z k) := by
  unfold heatTerm
  apply Differentiable.const_mul
  exact hf.contDiff.differentiable_iteratedDeriv' (2 * k)

/-- The derivative-series heat flow of an entire function of order below two is entire. -/
theorem differentiable_heatE (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (t : ℝ) : Differentiable ℂ (heatE t f) := by
  intro z₀
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  have hsum := (summable_majorant (C := 4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ))
    (by positivity) hδ).mul_left (A * Real.exp (B * 2 ^ ρ * (‖z₀‖ + 1) ^ ρ))
  have hdiff : DifferentiableOn ℂ (heatE t f) (ball 0 (‖z₀‖ + 1)) := by
    unfold heatE
    refine differentiableOn_tsum_of_summable_norm hsum
      (fun k => (differentiable_heatTerm hf t k).differentiableOn) isOpen_ball ?_
    intro k w hw
    rw [mem_ball_zero_iff] at hw
    exact norm_heatTerm_le_majorant hf hg hA hB hρ0 t (by positivity) hw.le k
  exact hdiff.differentiableAt (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))

end Soma.Holonics.RH.HeatFlowEntire
