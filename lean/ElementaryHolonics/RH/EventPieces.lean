import Mathlib
import ElementaryHolonics.RH.EventWindow

/-!
# RT3 (iii-g): the main term from below, the Gamma factor from above, and the horizontal pieces

In a strip `|Re s| ≤ X` with `‖s‖ ≥ 2`:
`‖g(s)‖ ≥ c_g(X) ‖s‖² ‖s‖^{−(X+1)/2} e^{−π‖s‖/2}` and `‖γ_t(s)‖ ≥ that · e^{−tπ²/4}`.
In the upper half-plane with `‖z‖ ≥ 2`:
`‖g(z)‖ ≤ (√(2π)/2) ‖z‖² ‖z‖^{(|Re z|+1)/2} (πe)^{|Re z|/2}` and `‖γ₁(z)‖ ≤ e^{π/4} ‖g(z)‖` when
`z/2` is in the sector. The horizontal piece of the rectangle is bounded by its length times the
supremum of `‖f‖` on it.
-/

noncomputable section

namespace Soma.Holonics.RH.EventPieces

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.FlowedGammaContour
open Soma.Holonics.RH.EventSaddle
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds

/-! ## The modulus of `g` -/

/-- The real part of `(z/2 − ½) Log(z/2) − z/2`. -/
theorem re_phase (z : ℂ) :
    ((z / 2 - 1 / 2) * Complex.log (z / 2) - z / 2).re =
      (z.re / 2 - 1 / 2) * Real.log (‖z‖ / 2) - z.im / 2 * Complex.arg (z / 2) - z.re / 2 := by
  have h1 : (z / 2 - 1 / 2 : ℂ).re = z.re / 2 - 1 / 2 := by simp
  have h2 : (z / 2 - 1 / 2 : ℂ).im = z.im / 2 := by simp
  have h3 : (Complex.log (z / 2)).re = Real.log (‖z‖ / 2) := by
    rw [Complex.log_re, norm_div, Complex.norm_ofNat]
  have h4 : (Complex.log (z / 2)).im = Complex.arg (z / 2) := Complex.log_im _
  have h5 : (z / 2 : ℂ).re = z.re / 2 := by simp
  rw [Complex.sub_re, Complex.mul_re, h1, h2, h3, h4, h5]

theorem norm_g_eq (z : ℂ) :
    ‖g z‖ = (1 / 4) * ‖z‖ * ‖z - 1‖ * Real.exp (-(z.re * Real.log π / 2)) * √(2 * π) *
      Real.exp ((z.re / 2 - 1 / 2) * Real.log (‖z‖ / 2) - z.im / 2 * Complex.arg (z / 2) - z.re / 2) := by
  unfold g
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by positivity)),
    re_phase]
  have h1 : (z * (-(Real.log π : ℂ) / 2)).re = -(z.re * Real.log π / 2) := by
    simp [Complex.mul_re]
    ring
  rw [h1, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
  ring

/-- The constant of the lower bound, `c_g(X) = (√(2π)/8) π^{−X/2} e^{−X/2}`. -/
def cg (X : ℝ) : ℝ := √(2 * π) / 8 * π ^ (-(X / 2)) * Real.exp (-(X / 2))

theorem cg_pos (X : ℝ) : 0 < cg X := by
  unfold cg
  have := Real.rpow_pos_of_pos Real.pi_pos (-(X / 2))
  positivity

/-- **The main term from below** in the strip `|Re s| ≤ X`, `‖s‖ ≥ 2`. -/
theorem norm_g_ge {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X) (hs : 2 ≤ ‖s‖) :
    cg X * ‖s‖ ^ 2 * ‖s‖ ^ (-((X + 1) / 2)) * Real.exp (-(π * ‖s‖ / 2)) ≤ ‖g s‖ := by
  rw [norm_g_eq]
  have hs0 : 0 < ‖s‖ := by linarith
  have hre : -X ≤ s.re := by linarith [neg_abs_le s.re]
  have hre' : s.re ≤ X := le_trans (le_abs_self _) hX
  have hlog : 0 ≤ Real.log (‖s‖ / 2) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (‖s‖ / 2) ≤ Real.log ‖s‖ :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogpos : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have harg : |Complex.arg (s / 2)| ≤ π := Complex.abs_arg_le_pi _
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  -- the exponent from below
  have hexp : -((X + 1) / 2) * Real.log ‖s‖ - π * ‖s‖ / 2 - X / 2 ≤
      (s.re / 2 - 1 / 2) * Real.log (‖s‖ / 2) - s.im / 2 * Complex.arg (s / 2) - s.re / 2 := by
    have h1 : -((X + 1) / 2) * Real.log ‖s‖ ≤ (s.re / 2 - 1 / 2) * Real.log (‖s‖ / 2) := by
      rcases le_or_gt 0 (s.re / 2 - 1 / 2) with hpos | hneg
      · calc -((X + 1) / 2) * Real.log ‖s‖ ≤ 0 := by
              apply mul_nonpos_of_nonpos_of_nonneg _ hlogpos
              linarith
          _ ≤ (s.re / 2 - 1 / 2) * Real.log (‖s‖ / 2) := mul_nonneg hpos hlog
      · calc -((X + 1) / 2) * Real.log ‖s‖ ≤ (s.re / 2 - 1 / 2) * Real.log ‖s‖ := by
              apply mul_le_mul_of_nonneg_right _ hlogpos
              linarith
          _ ≤ (s.re / 2 - 1 / 2) * Real.log (‖s‖ / 2) :=
              mul_le_mul_of_nonpos_left hlog2 hneg.le
    have h2 : -(π * ‖s‖ / 2) ≤ -(s.im / 2 * Complex.arg (s / 2)) := by
      have : s.im / 2 * Complex.arg (s / 2) ≤ π * ‖s‖ / 2 := by
        calc s.im / 2 * Complex.arg (s / 2) ≤ |s.im / 2 * Complex.arg (s / 2)| := le_abs_self _
          _ = |s.im| / 2 * |Complex.arg (s / 2)| := by rw [abs_mul, abs_div, abs_two]
          _ ≤ ‖s‖ / 2 * π := by gcongr
          _ = π * ‖s‖ / 2 := by ring
      linarith
    have h3 : -(X / 2) ≤ -(s.re / 2) := by linarith
    linarith
  have hexpπ : Real.exp (-(X * Real.log π / 2)) ≤ Real.exp (-(s.re * Real.log π / 2)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
    nlinarith
  have hs1 : ‖s‖ / 2 ≤ ‖s - 1‖ := norm_sub_one_ge hs
  have hrpow : ‖s‖ ^ (-((X + 1) / 2)) = Real.exp (-((X + 1) / 2) * Real.log ‖s‖) := by
    rw [Real.rpow_def_of_pos hs0]
    ring_nf
  have hπ : π ^ (-(X / 2)) = Real.exp (-(X * Real.log π / 2)) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]
    ring_nf
  unfold cg
  rw [hrpow, hπ]
  calc √(2 * π) / 8 * Real.exp (-(X * Real.log π / 2)) * Real.exp (-(X / 2)) * ‖s‖ ^ 2 *
        Real.exp (-((X + 1) / 2) * Real.log ‖s‖) * Real.exp (-(π * ‖s‖ / 2))
      = (1 / 4) * ‖s‖ * (‖s‖ / 2) * Real.exp (-(X * Real.log π / 2)) * √(2 * π) *
          Real.exp (-((X + 1) / 2) * Real.log ‖s‖ - π * ‖s‖ / 2 - X / 2) := by
        have e1 : Real.exp (-((X + 1) / 2) * Real.log ‖s‖ - π * ‖s‖ / 2 - X / 2) =
            Real.exp (-((X + 1) / 2) * Real.log ‖s‖) * Real.exp (-(π * ‖s‖ / 2)) *
              Real.exp (-(X / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          first | done | ring
        rw [e1]
        ring
    _ ≤ (1 / 4) * ‖s‖ * ‖s - 1‖ * Real.exp (-(s.re * Real.log π / 2)) * √(2 * π) *
          Real.exp ((s.re / 2 - 1 / 2) * Real.log (‖s‖ / 2) - s.im / 2 * Complex.arg (s / 2) -
            s.re / 2) := by
        gcongr

/-- **`γ_t(s)` from below.** -/
theorem norm_γt'_ge {t : ℝ} (ht : 0 ≤ t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    (hs : 2 ≤ ‖s‖) :
    cg X * ‖s‖ ^ 2 * ‖s‖ ^ (-((X + 1) / 2)) * Real.exp (-(π * ‖s‖ / 2)) *
      Real.exp (-(t * π ^ 2 / 4)) ≤ ‖γt' t s‖ := by
  unfold γt'
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul (norm_g_ge hX0 hX hs) _ (Real.exp_pos _).le (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hre : ((t : ℂ) * (Λs s) ^ 2 / 4).re = t * ((Λs s).re ^ 2 - (Λs s).im ^ 2) / 4 := by
    simp [Complex.mul_re, Complex.div_ofNat_re, sq] <;> ring
  rw [hre]
  have him : |(Λs s).im| ≤ π := by
    unfold Λs
    rw [Complex.sub_im, Complex.log_im, Complex.ofReal_im, sub_zero]
    exact Complex.abs_arg_le_pi _
  have him2 : (Λs s).im ^ 2 ≤ π ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) him 2
  first | done | nlinarith [sq_nonneg (Λs s).re]

/-- **`g` from above** in the upper half-plane with `‖z‖ ≥ 2`. -/
theorem norm_g_le {z : ℂ} (hz : 0 < z.im) (hz2 : 2 ≤ ‖z‖) :
    ‖g z‖ ≤ √(2 * π) / 2 * ‖z‖ ^ 2 * ‖z‖ ^ ((|z.re| + 1) / 2) * (π * Real.exp 1) ^ (|z.re| / 2) := by
  rw [norm_g_eq]
  have hz0 : 0 < ‖z‖ := by linarith
  have hlog : 0 ≤ Real.log (‖z‖ / 2) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (‖z‖ / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by linarith) (by linarith)
  have hlogpos : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
  have harg : 0 ≤ Complex.arg (z / 2) := by
    rw [Complex.arg_nonneg_iff]
    simp
    linarith
  have hz1 : ‖z - 1‖ ≤ 2 * ‖z‖ := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ + 1 := by rw [norm_one]
      _ ≤ 2 * ‖z‖ := by linarith
  have hexp : (z.re / 2 - 1 / 2) * Real.log (‖z‖ / 2) - z.im / 2 * Complex.arg (z / 2) - z.re / 2 ≤
      (|z.re| + 1) / 2 * Real.log ‖z‖ + |z.re| / 2 := by
    have h1 : (z.re / 2 - 1 / 2) * Real.log (‖z‖ / 2) ≤ (|z.re| + 1) / 2 * Real.log ‖z‖ := by
      calc (z.re / 2 - 1 / 2) * Real.log (‖z‖ / 2) ≤ |z.re / 2 - 1 / 2| * Real.log (‖z‖ / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hlog
        _ ≤ (|z.re| + 1) / 2 * Real.log ‖z‖ := by
            gcongr
            calc |z.re / 2 - 1 / 2| ≤ |z.re / 2| + |(1 / 2 : ℝ)| := abs_sub _ _
              _ = (|z.re| + 1) / 2 := by rw [abs_div, abs_two]; norm_num; ring
    have h2 : 0 ≤ z.im / 2 * Complex.arg (z / 2) := by positivity
    have h3 : -(z.re / 2) ≤ |z.re| / 2 := by linarith [neg_abs_le z.re]
    linarith
  have hexpπ : Real.exp (-(z.re * Real.log π / 2)) ≤ Real.exp (|z.re| * Real.log π / 2) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
    nlinarith [neg_abs_le z.re]
  have hrpow : ‖z‖ ^ ((|z.re| + 1) / 2) = Real.exp ((|z.re| + 1) / 2 * Real.log ‖z‖) := by
    rw [Real.rpow_def_of_pos hz0]
    ring_nf
  have hπe : (π * Real.exp 1) ^ (|z.re| / 2) = Real.exp (|z.re| * Real.log π / 2 + |z.re| / 2) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul Real.pi_pos.ne' (Real.exp_pos 1).ne',
      Real.log_exp]
    ring_nf
  rw [hrpow, hπe]
  calc (1 / 4) * ‖z‖ * ‖z - 1‖ * Real.exp (-(z.re * Real.log π / 2)) * √(2 * π) *
        Real.exp ((z.re / 2 - 1 / 2) * Real.log (‖z‖ / 2) - z.im / 2 * Complex.arg (z / 2) - z.re / 2)
      ≤ (1 / 4) * ‖z‖ * (2 * ‖z‖) * Real.exp (|z.re| * Real.log π / 2) * √(2 * π) *
          Real.exp ((|z.re| + 1) / 2 * Real.log ‖z‖ + |z.re| / 2) := by
        gcongr
    _ = √(2 * π) / 2 * ‖z‖ ^ 2 * Real.exp ((|z.re| + 1) / 2 * Real.log ‖z‖) *
          Real.exp (|z.re| * Real.log π / 2 + |z.re| / 2) := by
        rw [Real.exp_add, Real.exp_add]
        ring

/-- **`γ₁` from above**: `‖γ₁(z)‖ ≤ e^{π/4} ‖g(z)‖` when `z/2` is in the sector and `‖z‖ ≥ 2`. -/
theorem norm_γ₁_le_g {z : ℂ} (hsec : z / 2 ∈ Sector) (hz2 : 2 ≤ ‖z‖) :
    ‖γ₁ z‖ ≤ Real.exp (π / 4) * ‖g z‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz2
    linarith
  rw [γ₁_eq_γ hz0, γ_eq_g hsec, norm_mul, Complex.norm_exp, mul_comm]
  gcongr
  have h1 := norm_μ_le hsec
  have h2 : ‖z / 2‖ = ‖z‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  rw [h2] at h1
  have h3 : (-μ (z / 2)).re ≤ ‖μ (z / 2)‖ := by
    rw [Complex.neg_re]
    linarith [Complex.abs_re_le_norm (μ (z / 2)), neg_abs_le (μ (z / 2)).re]
  have h4 : π / (4 * (‖z‖ / 2)) ≤ π / 4 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  linarith

/-! ## The horizontal piece -/

/-- **A horizontal piece is bounded by its length times a supremum.** -/
theorem norm_horizontal_le {t : ℝ} (w : ℂ) (c y₁ M : ℝ)
    (hM : ∀ x : ℝ, x ∈ uIcc c 2 → ‖f t w ((x : ℂ) + (y₁ : ℂ) * Complex.I)‖ ≤ M) :
    ‖∫ x in c..(2 : ℝ), f t w ((x : ℂ) + (y₁ : ℂ) * Complex.I)‖ ≤ M * |2 - c| :=
  intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hM x (uIoc_subset_uIcc hx)

end Soma.Holonics.RH.EventPieces
