import Mathlib
import ElementaryHolonics.RH.EventBounds

/-!
# RT3 (iii-e): the full Gaussian of the saddle

`G = ∫_ℝ e^{−Av² + iqv} dv = (π/A)^{1/2} e^{−q²/(4A)}`, and with `δ = 2tℓ'(s)` (so `A = (1+δ)/(4t)`)
`(4πt)^{−1/2} G = e^{−½ Log(1+δ)} e^{−q²/(4A)}`, which is within `36t/‖s‖ + 4t‖q‖²` of `1`, while
`‖G‖ ≥ √(2πt) e^{−2t‖q‖²}`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventGaussian

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.FlowedGammaContour
open Soma.Holonics.RH.EventSaddle
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds

/-- `δ = 2tℓ'(s)`. -/
def δ (t : ℝ) (s : ℂ) : ℂ := 2 * t * ℓ' s

theorem A_eq {t : ℝ} (ht : 0 < t) (s : ℂ) : A t s = (1 + δ t s) / (4 * t) := by
  unfold A δ
  have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring

theorem norm_δ_le {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) : ‖δ t s‖ ≤ 6 * t / ‖s‖ := by
  unfold δ
  rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have := norm_ℓ'_le hs
  calc 2 * t * ‖ℓ' s‖ ≤ 2 * t * (3 / ‖s‖) := by gcongr
    _ = 6 * t / ‖s‖ := by ring

/-- The full Gaussian `G = ∫_ℝ gauss`. -/
def G (t : ℝ) (s : ℂ) (h : ℝ) : ℂ := ∫ v : ℝ, gauss t s h v

theorem integrable_gauss {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) (h : ℝ) :
    Integrable (gauss t s h) := by
  have hA : 0 < (A t s).re := lt_of_lt_of_le (by positivity) (re_A_ge ht hs hst)
  have := integrable_cexp_quadratic hA (Complex.I * q s h) 0
  refine this.congr (Eventually.of_forall fun v => ?_)
  unfold gauss
  simp only [add_zero]

/-- **The closed form**: `G = (π/A)^{1/2} e^{−q²/(4A)}`. -/
theorem G_eq {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) (h : ℝ) :
    G t s h = ((π : ℂ) / A t s) ^ (1 / 2 : ℂ) * Complex.exp (-(q s h) ^ 2 / (4 * A t s)) := by
  have hA : 0 < (A t s).re := lt_of_lt_of_le (by positivity) (re_A_ge ht hs hst)
  have hb : (-(A t s)).re < 0 := by simp; exact hA
  have hAne : A t s ≠ 0 := fun h0 => by rw [h0] at hA; simp at hA
  have h := integral_cexp_quadratic hb (Complex.I * q s h) 0
  unfold G gauss
  simp only [add_zero, zero_sub] at h
  rw [h, neg_neg]
  congr 1
  congr 1
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem one_add_δ_ne_zero {t : ℝ} {s : ℂ} (hδ : ‖δ t s‖ ≤ 1 / 2) : 1 + δ t s ≠ 0 := by
  intro h
  have : ‖δ t s‖ = 1 := by
    have h2 : δ t s = -1 := by linear_combination h
    rw [h2, norm_neg, norm_one]
  linarith

theorem re_one_add_δ_pos {t : ℝ} {s : ℂ} (hδ : ‖δ t s‖ ≤ 1 / 2) : 0 < (1 + δ t s).re := by
  rw [Complex.add_re, Complex.one_re]
  have := Complex.abs_re_le_norm (δ t s)
  linarith [neg_abs_le (δ t s).re]

theorem exp_half_log {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = √x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

/-- **The normalized Gaussian**: `(4πt)^{−1/2} G = e^{−½ Log(1+δ)} e^{−q²/(4A)}`. -/
theorem sqrt_G_eq {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖)
    (hδ : ‖δ t s‖ ≤ 1 / 2) (h : ℝ) :
    ((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s h =
      Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 + δ t s)) *
        Complex.exp (-(q s h) ^ 2 / (4 * A t s)) := by
  rw [G_eq ht hs hst h]
  have hne := one_add_δ_ne_zero hδ
  have hre := re_one_add_δ_pos hδ
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hpos : (0 : ℝ) < 4 * π * t := by positivity
  have hπA : (π : ℂ) / A t s = ((4 * π * t : ℝ) : ℂ) * (1 + δ t s)⁻¹ := by
    rw [A_eq ht s]
    push_cast
    field_simp
  have harg : (1 + δ t s).arg ≠ π := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith [h.1]
  have hlog : Complex.log ((π : ℂ) / A t s) = (Real.log (4 * π * t) : ℂ) - Complex.log (1 + δ t s) := by
    rw [hπA, Complex.log_ofReal_mul hpos (inv_ne_zero hne), Complex.log_inv _ harg]
    ring
  have hcpow : ((π : ℂ) / A t s) ^ (1 / 2 : ℂ) =
      ((√(4 * π * t) : ℝ) : ℂ) * Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 + δ t s)) := by
    have hne2 : (π : ℂ) / A t s ≠ 0 := by
      rw [hπA]
      exact mul_ne_zero (by exact_mod_cast hpos.ne') (inv_ne_zero hne)
    rw [Complex.cpow_def_of_ne_zero hne2, hlog, sub_mul, Complex.exp_sub]
    have hsq : Complex.exp ((Real.log (4 * π * t) : ℂ) * (1 / 2)) = ((√(4 * π * t) : ℝ) : ℂ) := by
      rw [show ((Real.log (4 * π * t) : ℝ) : ℂ) * (1 / 2) = ((Real.log (4 * π * t) / 2 : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_exp, exp_half_log hpos]
    rw [hsq]
    have : Complex.exp (Complex.log (1 + δ t s) * (1 / 2)) =
        (Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 + δ t s)))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      ring
    rw [this, div_inv_eq_mul]
  rw [hcpow]
  have hsC : ((√(4 * π * t) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  field_simp

theorem norm_log_one_add_le' {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖Complex.log (1 + z)‖ ≤ 2 * ‖z‖ := by
  have h := Complex.norm_log_one_add_le (by linarith : ‖z‖ < 1)
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖Complex.log (1 + z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := h
    _ ≤ ‖z‖ ^ 2 * 2 / 2 + ‖z‖ := by gcongr
    _ ≤ 2 * ‖z‖ := by nlinarith [norm_nonneg z]

/-- **The normalized Gaussian is close to one**:
`‖(4πt)^{−1/2} G − 1‖ ≤ 36t/‖s‖ + 4t‖q‖²` when `‖δ‖ ≤ ½` and `2t‖q‖² ≤ 1`. -/
theorem norm_sqrt_G_sub_one_le {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖)
    (hδ : ‖δ t s‖ ≤ 1 / 2) {h : ℝ} (hq : 2 * t * ‖q s h‖ ^ 2 ≤ 1) :
    ‖((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s h - 1‖ ≤ 36 * t / ‖s‖ + 4 * t * ‖q s h‖ ^ 2 := by
  rw [sqrt_G_eq ht hs hst hδ h]
  set a : ℂ := Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 + δ t s)) with ha
  set b : ℂ := Complex.exp (-(q s h) ^ 2 / (4 * A t s)) with hb
  have hA : 1 / (8 * t) ≤ (A t s).re := re_A_ge ht hs hst
  have hAn : 1 / (8 * t) ≤ ‖A t s‖ := hA.trans (Complex.re_le_norm _)
  have hAne : A t s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hAn
    have : 0 < 1 / (8 * t) := by positivity
    linarith
  -- `‖a − 1‖ ≤ ‖Log(1+δ)‖ ≤ 2‖δ‖ ≤ 12t/‖s‖`
  have hlog : ‖Complex.log (1 + δ t s)‖ ≤ 2 * ‖δ t s‖ := norm_log_one_add_le' hδ
  have hx1 : ‖-(1 / 2 : ℂ) * Complex.log (1 + δ t s)‖ ≤ 1 := by
    rw [norm_mul, norm_neg, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    linarith
  have ha1 : ‖a - 1‖ ≤ 12 * t / ‖s‖ := by
    rw [ha]
    calc ‖Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 + δ t s)) - 1‖
        ≤ 2 * ‖-(1 / 2 : ℂ) * Complex.log (1 + δ t s)‖ := Complex.norm_exp_sub_one_le hx1
      _ = ‖Complex.log (1 + δ t s)‖ := by
          rw [norm_mul, norm_neg, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
          ring
      _ ≤ 2 * ‖δ t s‖ := hlog
      _ ≤ 2 * (6 * t / ‖s‖) := by gcongr; exact norm_δ_le ht hs
      _ = 12 * t / ‖s‖ := by ring
  -- `‖q²/(4A)‖ ≤ 2t‖q‖²`
  have hx2 : ‖-(q s h) ^ 2 / (4 * A t s)‖ ≤ 2 * t * ‖q s h‖ ^ 2 := by
    rw [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_ofNat]
    rw [div_le_iff₀ (by positivity)]
    have : 2 * t * ‖q s h‖ ^ 2 * (4 * ‖A t s‖) = ‖q s h‖ ^ 2 * (8 * t * ‖A t s‖) := by ring
    rw [this]
    have h8 : 1 ≤ 8 * t * ‖A t s‖ := by
      rw [div_le_iff₀ (by positivity)] at hAn
      linarith
    nlinarith [sq_nonneg ‖q s h‖]
  have hb1 : ‖b - 1‖ ≤ 4 * t * ‖q s h‖ ^ 2 := by
    rw [hb]
    calc ‖Complex.exp (-(q s h) ^ 2 / (4 * A t s)) - 1‖
        ≤ 2 * ‖-(q s h) ^ 2 / (4 * A t s)‖ := Complex.norm_exp_sub_one_le (hx2.trans hq)
      _ ≤ 2 * (2 * t * ‖q s h‖ ^ 2) := by gcongr
      _ = 4 * t * ‖q s h‖ ^ 2 := by ring
  have hbn : ‖b‖ ≤ 3 := by
    have := norm_sub_norm_le b 1
    rw [norm_one] at this
    linarith
  calc ‖a * b - 1‖ = ‖(a - 1) * b + (b - 1)‖ := by ring_nf
    _ ≤ ‖(a - 1) * b‖ + ‖b - 1‖ := norm_add_le _ _
    _ = ‖a - 1‖ * ‖b‖ + ‖b - 1‖ := by rw [norm_mul]
    _ ≤ (12 * t / ‖s‖) * 3 + 4 * t * ‖q s h‖ ^ 2 := by gcongr
    _ = 36 * t / ‖s‖ + 4 * t * ‖q s h‖ ^ 2 := by ring

/-- **The full Gaussian is not small**: `‖G‖ ≥ √(2πt) e^{−2t‖q‖²}`. -/
theorem norm_G_ge {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) (h : ℝ) :
    √(2 * π * t) * Real.exp (-(2 * t * ‖q s h‖ ^ 2)) ≤ ‖G t s h‖ := by
  rw [G_eq ht hs hst h, norm_mul]
  have hA : 1 / (8 * t) ≤ (A t s).re := re_A_ge ht hs hst
  have hAn : 1 / (8 * t) ≤ ‖A t s‖ := hA.trans (Complex.re_le_norm _)
  have hAne : A t s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hAn
    have : 0 < 1 / (8 * t) := by positivity
    linarith
  have hAle := norm_A_le ht hs hst
  have hne : (π : ℂ) / A t s ≠ 0 := div_ne_zero (by exact_mod_cast Real.pi_pos.ne') hAne
  have h1 : ‖((π : ℂ) / A t s) ^ (1 / 2 : ℂ)‖ = ‖(π : ℂ) / A t s‖ ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hne]
    simp
  have h2 : √(2 * π * t) ≤ ‖(π : ℂ) / A t s‖ ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [le_div_iff₀ (norm_pos_iff.mpr hAne)]
    calc 2 * π * t * ‖A t s‖ ≤ 2 * π * t * (1 / (2 * t)) := by gcongr
      _ = π := by field_simp
  have h3 : Real.exp (-(2 * t * ‖q s h‖ ^ 2)) ≤ ‖Complex.exp (-(q s h) ^ 2 / (4 * A t s))‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre := Complex.abs_re_le_norm (-(q s h) ^ 2 / (4 * A t s))
    have hx2 : ‖-(q s h) ^ 2 / (4 * A t s)‖ ≤ 2 * t * ‖q s h‖ ^ 2 := by
      rw [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_ofNat]
      rw [div_le_iff₀ (by positivity)]
      have : 2 * t * ‖q s h‖ ^ 2 * (4 * ‖A t s‖) = ‖q s h‖ ^ 2 * (8 * t * ‖A t s‖) := by ring
      rw [this]
      have h8 : 1 ≤ 8 * t * ‖A t s‖ := by
        rw [div_le_iff₀ (by positivity)] at hAn
        linarith
      nlinarith [sq_nonneg ‖q s h‖]
    linarith [neg_abs_le (-(q s h) ^ 2 / (4 * A t s)).re]
  rw [h1]
  exact mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)

end Soma.Holonics.RH.EventGaussian
