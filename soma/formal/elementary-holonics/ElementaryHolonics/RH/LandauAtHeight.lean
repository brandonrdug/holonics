import ElementaryHolonics.RH.JensenCountsTheComb
import ElementaryHolonics.RH.XiLowerBoundOnLineTwo

/-!
# Landau's lemma for `ξ` at height, with an explicit budget

At the base point `2 + iτ` (`|τ| ≥ 2`) and radius `r`, the growth bound on `ξ` and the lower
bound `log |ξ(2 + iτ)| ≥ −(|τ| + 2)` make the Landau budget explicit:
`heightBudget C r τ = max 1 (C (5 + |τ| + r) log(5 + |τ| + r) + |τ| + 2)`, and Jensen's count of
the zeros in the half disc is at most `heightCount = (heightBudget + |τ| + 2) / log(3/2)`.  Both
are polynomial in the height, which is all the horizontal-edge bound needs.
-/

open Complex Metric Set
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.AbscissaGrowth
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.ZeroFactorizationExists
open Soma.Holonics.RH.LandauXi
open Soma.Holonics.RH.JensenCountsTheComb
open Soma.Holonics.RH.XiLowerBoundOnLineTwo
open Soma.Holonics.RH.XiEdgeDecomposition

namespace Soma.Holonics.RH.LandauAtHeight

/-- The explicit Landau budget at height `τ` and radius `r`. -/
noncomputable def heightBudget (C r τ : ℝ) : ℝ :=
  max 1 (C * (2 + |τ| + r + 3) * Real.log (2 + |τ| + r + 3) + (|τ| + 2))

/-- The explicit Jensen count at height `τ` and radius `r`. -/
noncomputable def heightCount (C r τ : ℝ) : ℝ :=
  (heightBudget C r τ + |τ| + 2) / Real.log (3 / 2)

theorem one_le_heightBudget (C r τ : ℝ) : 1 ≤ heightBudget C r τ := le_max_left _ _

theorem heightCount_nonneg (C r τ : ℝ) : 0 ≤ heightCount C r τ := by
  unfold heightCount
  apply div_nonneg
  · linarith [one_le_heightBudget C r τ, abs_nonneg τ]
  · exact (Real.log_pos (by norm_num)).le

theorem norm_two_add_le (τ : ℝ) : ‖(2 + (τ : ℂ) * I)‖ ≤ 2 + |τ| := by
  calc ‖(2 : ℂ) + τ * I‖ ≤ ‖(2 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
    _ = 2 + |τ| := by simp

theorem riemannXi_two_add_ne_zero (τ : ℝ) : riemannXi (2 + τ * I) ≠ 0 := by
  have hre : (2 + (τ : ℂ) * I).re = 2 := by simp
  have hs : 1 < (2 + (τ : ℂ) * I).re := by rw [hre]; norm_num
  rw [riemannXi_eq_mul_zeta hs]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (XiEdgeDecomposition.ne_zero_of_one_lt_re hs))
    (sub_ne_zero.mpr (XiEdgeDecomposition.ne_one_of_one_lt_re hs)))
    (Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num))) (riemannZeta_ne_zero_of_one_lt_re hs)

theorem xiBudget_le {C r τ : ℝ} (hC : 0 < C) (hr : 0 < r) (hτ : 2 ≤ |τ|) :
    xiBudget C (2 + τ * I) r ≤ heightBudget C r τ := by
  unfold xiBudget heightBudget
  apply max_le_max le_rfl
  have hz := norm_two_add_le τ
  have hlow := log_norm_riemannXi_two_add_ge hτ
  have h1 : 1 ≤ ‖(2 + (τ : ℂ) * I)‖ + r + 3 := by linarith [norm_nonneg (2 + (τ : ℂ) * I)]
  have hmono := mulLog_mono_on_one h1
    (by linarith : ‖(2 + (τ : ℂ) * I)‖ + r + 3 ≤ 2 + |τ| + r + 3)
  have := mul_le_mul_of_nonneg_left hmono hC.le
  rw [mul_assoc, mul_assoc]
  linarith

theorem log_jensen_le {C r τ : ℝ} (hC : 0 < C) (hr : 0 < r) (hτ : 2 ≤ |τ|) :
    Real.log (jensenCeiling C (2 + τ * I) r / ‖riemannXi (2 + τ * I)‖) ≤
      heightBudget C r τ + |τ| + 2 := by
  have hξ := riemannXi_two_add_ne_zero τ
  have ha : 0 < ‖riemannXi (2 + τ * I)‖ := norm_pos_iff.mpr hξ
  have hlow := log_norm_riemannXi_two_add_ge hτ
  have hB := xiBudget_le hC hr hτ
  rw [Real.log_div (lt_of_lt_of_le one_pos (one_le_jensenCeiling C _ r)).ne' ha.ne']
  unfold jensenCeiling
  rcases le_total 1 (‖riemannXi (2 + τ * I)‖ * Real.exp (xiBudget C (2 + τ * I) r)) with h | h
  · rw [max_eq_right h, Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith [abs_nonneg τ]
  · rw [max_eq_left h, Real.log_one]
    linarith [one_le_heightBudget C r τ]

/-- **Landau at height.**  At the base point `2 + iτ` with `|τ| ≥ 2` and radius `r`, `ξ` has a
zero factorization whose count is at most `heightCount`, and whose flux remainder on the eighth
disc is bounded by `16 (heightBudget + heightCount · log 2) / r`. -/
theorem exists_zeroFactorization_at_height {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, Real.log ‖riemannXi z‖ ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3))
    {r τ : ℝ} (hr : 0 < r) (hτ : 2 ≤ |τ|) :
    ∃ Z : ZeroFactorization riemannXi (2 + τ * I) r,
      (Z.count : ℝ) ≤ heightCount C r τ ∧
      ∀ z ∈ closedBall (2 + τ * I) (r / 8), riemannXi z ≠ 0 →
        ‖logDeriv riemannXi z - ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ ≤
          16 * (heightBudget C r τ + heightCount C r τ * Real.log 2) / r := by
  have hξ₀ := riemannXi_two_add_ne_zero τ
  obtain ⟨Z, hcount⟩ := exists_zeroFactorization_count differentiable_riemannXi hr hξ₀
  have hN : (Z.count : ℝ) ≤
      Real.log (jensenCeiling C (2 + τ * I) r / ‖riemannXi (2 + τ * I)‖) / Real.log (3 / 2) := by
    have h := finsum_divisor_le hC hgrowth hr hξ₀
    rw [← hcount] at h
    exact_mod_cast h
  have hN' : (Z.count : ℝ) ≤ heightCount C r τ :=
    hN.trans (div_le_div_of_nonneg_right (log_jensen_le hC hr hτ)
      (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)).le)
  refine ⟨Z, hN', fun z hz hfz => ?_⟩
  have hL := Z.norm_logDeriv_sub_flux_le hr (xiBudget_pos C _ r) hξ₀
    (fun w hw => norm_riemannXi_le_of_growth hC hgrowth hr hξ₀ hw) hz hfz
  refine hL.trans ?_
  apply div_le_div_of_nonneg_right _ hr.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := mul_le_mul_of_nonneg_right hN' hlog2
  linarith [xiBudget_le hC hr hτ]

end Soma.Holonics.RH.LandauAtHeight
