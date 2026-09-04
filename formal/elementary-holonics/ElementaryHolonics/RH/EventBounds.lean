import Mathlib
import ElementaryHolonics.RH.EventMain

/-!
# RT3 (iii-d): the elementary bounds

The bounds the saddle estimates are made of: `‖ε₁(s)‖ ≤ 3/‖s‖`, `‖ℓ'(s)‖ ≤ 3/‖s‖`,
`‖Λ(s)‖ ≤ log ‖s‖ + 5`, `|e^{−tΛ(s)L}| ≤ 1` for `‖s‖ ≥ 2π`, the Gaussian's modulus,
the lower bound for `|g(s)|` in a strip and the upper bound for `|g(z)|` in the upper half-plane,
`|γ₁(2 + iy)| ≤ (1 + |y|)/(2π)`, and two Gaussian integral estimates (the tail and the cubic
moment).
-/

noncomputable section

namespace Soma.Holonics.RH.EventBounds

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.FlowedGammaContour
open Soma.Holonics.RH.EventSaddle
open Soma.Holonics.RH.EventMain

/-! ## The rational coefficients -/

theorem norm_sub_one_ge {s : ℂ} (hs : 2 ≤ ‖s‖) : ‖s‖ / 2 ≤ ‖s - 1‖ := by
  have := norm_sub_norm_le s 1
  rw [norm_one] at this
  linarith

theorem norm_ε₁_le {s : ℂ} (hs : 2 ≤ ‖s‖) : ‖ε₁ s‖ ≤ 3 / ‖s‖ := by
  have hs0 : 0 < ‖s‖ := by linarith
  have h1 : ‖(2 * s)⁻¹‖ = 1 / (2 * ‖s‖) := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat, one_div]
  have h2 : ‖(s - 1)⁻¹‖ ≤ 2 / ‖s‖ := by
    rw [norm_inv]
    have := norm_sub_one_ge hs
    calc ‖s - 1‖⁻¹ ≤ (‖s‖ / 2)⁻¹ := inv_anti₀ (by linarith) this
      _ = 2 / ‖s‖ := by rw [inv_div]
  unfold ε₁
  calc ‖(2 * s)⁻¹ + (s - 1)⁻¹‖ ≤ ‖(2 * s)⁻¹‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
    _ ≤ 1 / (2 * ‖s‖) + 2 / ‖s‖ := by rw [h1]; gcongr
    _ ≤ 3 / ‖s‖ := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hs0]
        nlinarith

theorem norm_ℓ'_le {s : ℂ} (hs : 2 ≤ ‖s‖) : ‖ℓ' s‖ ≤ 3 / ‖s‖ := by
  have hs0 : 0 < ‖s‖ := by linarith
  have hs1 := norm_sub_one_ge hs
  have h1 : ‖1 / (2 * s)‖ = 1 / (2 * ‖s‖) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
  have h2 : ‖1 / (2 * s ^ 2)‖ = 1 / (2 * ‖s‖ ^ 2) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, norm_pow]
  have h3 : ‖1 / (s - 1) ^ 2‖ ≤ 4 / ‖s‖ ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    rw [div_le_div_iff₀ (pow_pos (by linarith [norm_sub_one_ge hs]) 2) (pow_pos hs0 2)]
    nlinarith [norm_nonneg (s - 1)]
  unfold ℓ'
  calc ‖1 / (2 * s) - 1 / (2 * s ^ 2) - 1 / (s - 1) ^ 2‖
      ≤ ‖1 / (2 * s)‖ + ‖1 / (2 * s ^ 2)‖ + ‖1 / (s - 1) ^ 2‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 1 / (2 * ‖s‖) + 1 / (2 * ‖s‖ ^ 2) + 4 / ‖s‖ ^ 2 := by rw [h1, h2]; gcongr
    _ ≤ 3 / ‖s‖ := by
        have e1 : 1 / (2 * ‖s‖ ^ 2) ≤ 1 / (4 * ‖s‖) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have e2 : 4 / ‖s‖ ^ 2 ≤ 2 / ‖s‖ := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have e3 : 1 / (2 * ‖s‖) + 1 / (4 * ‖s‖) + 2 / ‖s‖ ≤ 3 / ‖s‖ := by
          have : 1 / (2 * ‖s‖) + 1 / (4 * ‖s‖) + 2 / ‖s‖ = (11 / 4) / ‖s‖ := by
            field_simp
            ring
          rw [this]
          exact div_le_div_of_nonneg_right (by norm_num) hs0.le
        linarith

theorem norm_Λ_le {s : ℂ} (hs : 2 ≤ ‖s‖) : ‖Λs s‖ ≤ Real.log ‖s‖ + 6 := by
  unfold Λs
  have hs0 : 0 < ‖s‖ := by linarith
  have hlog : ‖Complex.log (s / 2)‖ ≤ Real.log ‖s‖ + π := by
    have h := Complex.norm_le_abs_re_add_abs_im (Complex.log (s / 2))
    rw [Complex.log_re, Complex.log_im, norm_div, Complex.norm_ofNat] at h
    have h1 : |Real.log (‖s‖ / 2)| ≤ Real.log ‖s‖ := by
      have hlog2 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hs
      have hpos2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rw [Real.log_div hs0.ne' two_ne_zero, abs_of_nonneg (by linarith)]
      linarith
    have h2 : |Complex.arg (s / 2)| ≤ π := Complex.abs_arg_le_pi _
    linarith
  calc ‖Complex.log (s / 2) - (Real.log π : ℂ)‖ ≤ ‖Complex.log (s / 2)‖ + ‖(Real.log π : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ (Real.log ‖s‖ + π) + Real.log π := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
        gcongr
    _ ≤ Real.log ‖s‖ + 6 := by
        have h4 : (4 : ℝ) < Real.exp 2 := by
          have := Real.exp_one_gt_d9
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith
        have h1 : Real.log π < 2 := by
          rw [Real.log_lt_iff_lt_exp Real.pi_pos]
          linarith [Real.pi_lt_four]
        linarith [Real.pi_lt_four]

/-- `|e^{−t Λ(s) L}| ≤ 1` for `‖s‖ ≥ 2π`, `t L ≥ 0`. -/
theorem norm_exp_neg_tΛ_le {s : ℂ} (hs : 2 * π ≤ ‖s‖) {t L : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L) :
    ‖Complex.exp (-(t : ℂ) * Λs s * L)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-(t : ℂ) * Λs s * L).re = -(t * L) * (Λs s).re := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hre]
  have hΛre : 0 ≤ (Λs s).re := by
    unfold Λs
    rw [Complex.sub_re, Complex.log_re, Complex.ofReal_re, norm_div, Complex.norm_ofNat]
    have hs0 : 0 < ‖s‖ / 2 := by linarith [Real.pi_pos]
    rw [sub_nonneg]
    apply Real.log_le_log Real.pi_pos
    linarith
  have := mul_nonneg (mul_nonneg ht hL) hΛre
  linarith

/-! ## The Gaussian -/

theorem re_A_ge {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) :
    1 / (8 * t) ≤ (A t s).re := by
  unfold A
  rw [Complex.add_re]
  have h1 : (1 / (4 * (t : ℂ))).re = 1 / (4 * t) := by
    have e : (1 / (4 * (t : ℂ))) = ((1 / (4 * t) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.ofReal_re]
  have h2 : |(ℓ' s / 2).re| ≤ 3 / (2 * ‖s‖) := by
    calc |(ℓ' s / 2).re| ≤ ‖ℓ' s / 2‖ := Complex.abs_re_le_norm _
      _ = ‖ℓ' s‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
      _ ≤ 3 / ‖s‖ / 2 := by gcongr; exact norm_ℓ'_le hs
      _ = 3 / (2 * ‖s‖) := by ring
  have h3 : 3 / (2 * ‖s‖) ≤ 1 / (8 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [h1]
  have e : 1 / (4 * t) = 2 * (1 / (8 * t)) := by
    field_simp
    ring
  linarith [neg_abs_le ((ℓ' s / 2).re)]

theorem norm_A_le {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) :
    ‖A t s‖ ≤ 1 / (2 * t) := by
  unfold A
  have h1 : ‖1 / (4 * (t : ℂ))‖ = 1 / (4 * t) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
  calc ‖1 / (4 * (t : ℂ)) + ℓ' s / 2‖ ≤ ‖1 / (4 * (t : ℂ))‖ + ‖ℓ' s / 2‖ := norm_add_le _ _
    _ ≤ 1 / (4 * t) + 3 / ‖s‖ / 2 := by
        rw [h1, norm_div, Complex.norm_ofNat]
        gcongr
        exact norm_ℓ'_le hs
    _ ≤ 1 / (4 * t) + 1 / (4 * t) := by
        have : 3 / ‖s‖ / 2 ≤ 1 / (4 * t) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
    _ = 1 / (2 * t) := by ring

theorem norm_q_le {s : ℂ} (hs : 2 ≤ ‖s‖) {h : ℝ} (hh : 0 ≤ h) : ‖q s h‖ ≤ (3 + 3 * h) / ‖s‖ := by
  unfold q
  calc ‖ε₁ s + h * ℓ' s‖ ≤ ‖ε₁ s‖ + ‖(h : ℂ) * ℓ' s‖ := norm_add_le _ _
    _ ≤ 3 / ‖s‖ + h * (3 / ‖s‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
        gcongr
        · exact norm_ε₁_le hs
        · exact norm_ℓ'_le hs
    _ = (3 + 3 * h) / ‖s‖ := by ring

/-- The modulus of the Gaussian: `‖gauss(v)‖ ≤ e^{−Re(A) v² + ‖q‖ |v|}`. -/
theorem norm_gauss_le (t : ℝ) (s : ℂ) (h v : ℝ) :
    ‖gauss t s h v‖ ≤ Real.exp (-(A t s).re * v ^ 2 + ‖q s h‖ * |v|) := by
  unfold gauss
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (-(A t s) * (v : ℂ) ^ 2 + Complex.I * q s h * v).re =
      -(A t s).re * v ^ 2 - (q s h).im * v := by
    simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
    ring
  rw [hre]
  have : -(q s h).im * v ≤ ‖q s h‖ * |v| := by
    calc -(q s h).im * v ≤ |(q s h).im * v| := by
          rw [← abs_neg, neg_mul]
          exact le_abs_self _
      _ = |(q s h).im| * |v| := abs_mul _ _
      _ ≤ ‖q s h‖ * |v| := by gcongr; exact Complex.abs_im_le_norm _
  linarith

/-! ## Gaussian integrals -/

/-- The tail of a Gaussian beyond `Y ≥ 0`: `∫_{v ≥ Y} e^{−c v²} ≤ √(2π/c) e^{−c Y²/2}`. -/
theorem gaussian_tail {c Y : ℝ} (hc : 0 < c) (hY : 0 ≤ Y) :
    ∫ v in Ioi Y, Real.exp (-c * v ^ 2) ≤ √(2 * π / c) * Real.exp (-(c / 2) * Y ^ 2) := by
  have hint : IntegrableOn (fun v : ℝ => Real.exp (-(c / 2) * v ^ 2)) (Ioi Y) :=
    (integrable_exp_neg_mul_sq (by positivity)).integrableOn
  calc ∫ v in Ioi Y, Real.exp (-c * v ^ 2)
      ≤ ∫ v in Ioi Y, Real.exp (-(c / 2) * Y ^ 2) * Real.exp (-(c / 2) * v ^ 2) := by
        apply setIntegral_mono_on (integrable_exp_neg_mul_sq hc).integrableOn
          (hint.const_mul _) measurableSet_Ioi
        intro v hv
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : Y ^ 2 ≤ v ^ 2 := by
          have hv' : Y ≤ v := le_of_lt hv
          nlinarith
        nlinarith
    _ = Real.exp (-(c / 2) * Y ^ 2) * ∫ v in Ioi Y, Real.exp (-(c / 2) * v ^ 2) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ Real.exp (-(c / 2) * Y ^ 2) * ∫ v : ℝ, Real.exp (-(c / 2) * v ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact setIntegral_le_integral (integrable_exp_neg_mul_sq (by positivity))
          (Eventually.of_forall fun v => (Real.exp_pos _).le)
    _ = √(2 * π / c) * Real.exp (-(c / 2) * Y ^ 2) := by
        rw [integral_gaussian, mul_comm]
        congr 2
        field_simp

/-- The cubic moment is dominated by a wider Gaussian:
`|v|³ e^{−c v²} ≤ 7 c^{−3/2} e^{−3 c v²/4}`. -/
theorem cube_mul_exp_le' {c : ℝ} (hc : 0 < c) (v : ℝ) :
    |v| ^ 3 * Real.exp (-c * v ^ 2) ≤ 7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(3 * c / 4) * v ^ 2) := by
  -- `(c v²/2)³/6 ≤ e^{c v²/2}` gives `|v|³ ≤ √48 c^{−3/2} e^{c v²/4}`
  have hx : 0 ≤ c * v ^ 2 / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (c * v ^ 2 / 2) hx 3
  have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3] at h
  -- so `(c v²)³ ≤ 48 e^{c v²/2}`
  have h6 : (c * v ^ 2) ^ 3 ≤ 48 * Real.exp (c * v ^ 2 / 2) := by
    have : (c * v ^ 2 / 2) ^ 3 / 6 = (c * v ^ 2) ^ 3 / 48 := by ring
    rw [this] at h
    linarith
  have hc32 : c ^ (-(3 / 2 : ℝ)) * c ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hc]
    norm_num
  have hE : 0 < Real.exp (-c * v ^ 2) := Real.exp_pos _
  -- `|v|³ ≤ 7 c^{-3/2} e^{c v²/4}`
  have key : |v| ^ 3 ≤ 7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (c * v ^ 2 / 4) := by
    have h7 : (v ^ 2) ^ 3 ≤ (7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (c * v ^ 2 / 4)) ^ 2 := by
      have hl : (v ^ 2) ^ 3 = (c * v ^ 2) ^ 3 * (c ^ (-(3 / 2 : ℝ))) ^ 2 := by
        have : (c ^ (-(3 / 2 : ℝ))) ^ 2 = (c ^ 3)⁻¹ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le,
            show (-(3 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
            Real.rpow_neg hc.le, Real.rpow_natCast]
        rw [this]
        field_simp
        first | done | ring
      have hr : (7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (c * v ^ 2 / 4)) ^ 2 =
          49 * (c ^ (-(3 / 2 : ℝ))) ^ 2 * Real.exp (c * v ^ 2 / 2) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
        push_cast
        ring_nf
      rw [hl, hr]
      have : 0 ≤ (c ^ (-(3 / 2 : ℝ))) ^ 2 := by positivity
      nlinarith
    have hpos : 0 ≤ 7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (c * v ^ 2 / 4) := by positivity
    have hsq : (|v| ^ 3) ^ 2 ≤ (7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (c * v ^ 2 / 4)) ^ 2 := by
      calc (|v| ^ 3) ^ 2 = (v ^ 2) ^ 3 := by rw [← sq_abs v]; ring
        _ ≤ _ := h7
    exact (pow_le_pow_iff_left₀ (a := |v| ^ 3) (b := 7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (c * v ^ 2 / 4))
      (by positivity) hpos two_ne_zero).mp hsq
  calc |v| ^ 3 * Real.exp (-c * v ^ 2)
      ≤ 7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (c * v ^ 2 / 4) * Real.exp (-c * v ^ 2) := by gcongr
    _ = 7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(3 * c / 4) * v ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2 <;> ring

/-! ## The Gamma factor on the line `Re z = 2` -/

theorem norm_γ₁_two (y : ℝ) : ‖γ₁ (2 + Complex.I * y)‖ ≤ (1 + |y|) / (2 * π) := by
  unfold γ₁
  have h1 : ‖(2 + Complex.I * y - 1 : ℂ)‖ ≤ 1 + |y| := by
    calc ‖(2 + Complex.I * y - 1 : ℂ)‖ = ‖(1 : ℂ) + Complex.I * y‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * y‖ := norm_add_le _ _
      _ = 1 + |y| := by simp
  have h2 : ‖(π : ℂ) ^ (-(2 + Complex.I * y) / 2)‖ = π⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have : (-(2 + Complex.I * (y : ℂ)) / 2).re = -1 := by simp <;> norm_num
    rw [this, Real.rpow_neg_one]
  have h3 : ‖Complex.Gamma ((2 + Complex.I * y) / 2 + 1)‖ ≤ 1 := by
    have hre : ((2 + Complex.I * (y : ℂ)) / 2 + 1).re = 2 := by simp <;> norm_num
    have := Soma.Holonics.RH.GammaBound.theGammaMagnitudeIsControlledByTheRealPart
      (s := (2 + Complex.I * (y : ℂ)) / 2 + 1) (by rw [hre]; norm_num)
    rw [hre, Real.Gamma_two] at this
    exact this
  calc ‖(1 / 2 : ℂ) * (2 + Complex.I * y - 1) *
        ((π : ℂ) ^ (-(2 + Complex.I * y) / 2) * Complex.Gamma ((2 + Complex.I * y) / 2 + 1))‖
      = (1 / 2) * ‖(2 + Complex.I * y - 1 : ℂ)‖ *
          (‖(π : ℂ) ^ (-(2 + Complex.I * y) / 2)‖ * ‖Complex.Gamma ((2 + Complex.I * y) / 2 + 1)‖) := by
        rw [norm_mul, norm_mul, norm_mul]
        norm_num
    _ ≤ (1 / 2) * (1 + |y|) * (π⁻¹ * 1) := by
        rw [h2]
        gcongr
    _ = (1 + |y|) / (2 * π) := by
        field_simp

end Soma.Holonics.RH.EventBounds
