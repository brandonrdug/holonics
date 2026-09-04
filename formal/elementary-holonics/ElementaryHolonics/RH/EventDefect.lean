import Mathlib
import ElementaryHolonics.RH.EventAssembly

/-!
# RT3 (iii-j): the relative defect from its four pieces

`‖r‖ ≤ (a(1 + b) + b)(1 + d) + d + e` where `a ≥ ‖F₁ − 1‖`, `b ≥ ‖G₀ − 1‖`, `d ≥ ‖I_W − G‖/‖G‖`,
`e ≥ ‖R'‖`; with `I_W − G = ∫ gauss·D + (∫_{−Y}^{Y} gauss − G)` and
`‖F₁ − 1‖ ≤ 2(6tL + 6t²L²)/‖s‖`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventDefect

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.FlowedGammaContour
open Soma.Holonics.RH.EventSaddle
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventGaussian
open Soma.Holonics.RH.EventWindow
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventTail
open Soma.Holonics.RH.EventAssembly

/-! ## Continuity on the window -/

theorem continuousOn_f_window {t : ℝ} (w s : ℂ) (h Y : ℝ) (hy : Y < s.im) :
    ContinuousOn (fun v : ℝ => f t w (s + h + Complex.I * v)) (Icc (-Y) Y) := by
  intro v hv
  have him : (s + h + Complex.I * v).im ≠ 0 := by
    simp
    linarith [hv.1]
  have hc : Continuous fun v : ℝ => s + h + Complex.I * (v : ℂ) := by fun_prop
  exact (ContinuousAt.comp (g := f t w) (f := fun v : ℝ => s + h + Complex.I * (v : ℂ))
    (differentiableAt_f w him).continuousAt hc.continuousAt).continuousWithinAt

theorem continuous_gauss (t : ℝ) (s : ℂ) (h : ℝ) : Continuous (gauss t s h) := by
  unfold gauss
  fun_prop

theorem continuousOn_D {t : ℝ} {s : ℂ} (hg : g s ≠ 0) (h Y : ℝ) (hy : Y < s.im) :
    ContinuousOn (fun v : ℝ => D t s h v) (Icc (-Y) Y) := by
  unfold D
  apply ContinuousOn.sub _ continuousOn_const
  apply ContinuousOn.div (continuousOn_f_window (J t s + h) s h Y hy)
    (continuousOn_const.mul (continuous_gauss t s h).continuousOn)
  intro v _
  exact mul_ne_zero (mul_ne_zero hg (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)

/-- `I_W − G = ∫_{−Y}^{Y} gauss·D + (∫_{−Y}^{Y} gauss − G)`. -/
theorem IW_sub_G {t : ℝ} {s : ℂ} (hg : g s ≠ 0) (h : ℝ) {Y : ℝ} (hY : 0 ≤ Y) (hy : Y < s.im) :
    IW t s h Y - G t s h =
      (∫ v in (-Y)..Y, gauss t s h v * D t s h v) - (G t s h - ∫ v in (-Y)..Y, gauss t s h v) := by
  unfold IW
  have h1 : IntervalIntegrable (gauss t s h) volume (-Y) Y :=
    (continuous_gauss t s h).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun v => gauss t s h v * D t s h v) volume (-Y) Y := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact (continuous_gauss t s h).continuousOn.mul (continuousOn_D hg h Y hy)
  have : ∫ v in (-Y)..Y, gauss t s h v * (1 + D t s h v) =
      (∫ v in (-Y)..Y, gauss t s h v) + ∫ v in (-Y)..Y, gauss t s h v * D t s h v := by
    rw [← intervalIntegral.integral_add h1 h2]
    congr 1
    funext v
    ring
  rw [this]
  ring

/-! ## The pieces -/

theorem norm_F₁_sub_one_le {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 2 ≤ ‖s‖) {L : ℝ} (hL : 0 ≤ L)
    (hsmall : (6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖ ≤ 1) :
    ‖F₁ t s L - 1‖ ≤ 2 * ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖) := by
  unfold F₁
  have hE : ‖(2 : ℂ) * t * L * ε₁ s + 2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s‖ ≤
      (6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖ := by
    calc ‖(2 : ℂ) * t * L * ε₁ s + 2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s‖
        ≤ ‖(2 : ℂ) * t * L * ε₁ s‖ + ‖2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s‖ := norm_add_le _ _
      _ = 2 * t * L * ‖ε₁ s‖ + 2 * t ^ 2 * L ^ 2 * ‖ℓ' s‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
          simp [abs_of_nonneg ht, abs_of_nonneg hL]
      _ ≤ 2 * t * L * (3 / ‖s‖) + 2 * t ^ 2 * L ^ 2 * (3 / ‖s‖) := by
          gcongr
          · exact norm_ε₁_le hs
          · exact norm_ℓ'_le hs
      _ = (6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖ := by ring
  calc ‖Complex.exp ((2 : ℂ) * t * L * ε₁ s + 2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s) - 1‖
      ≤ 2 * ‖(2 : ℂ) * t * L * ε₁ s + 2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s‖ :=
        Complex.norm_exp_sub_one_le (hE.trans hsmall)
    _ ≤ 2 * ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖) := by gcongr

/-- **The relative defect from its four pieces.** -/
theorem norm_rdef_le {t : ℝ} {s : ℂ} {L Y : ℝ} {a b d e : ℝ}
    (hG : G t s (2 * t * L) ≠ 0)
    (ha : ‖F₁ t s L - 1‖ ≤ a)
    (hb : ‖((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L) - 1‖ ≤ b)
    (hd : ‖IW t s (2 * t * L) Y - G t s (2 * t * L)‖ ≤ d * ‖G t s (2 * t * L)‖)
    (he : ‖Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      (-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y) / γt' t s‖ ≤ e) :
    ‖rdef t s L Y‖ ≤ (a * (1 + b) + b) * (1 + d) + d + e := by
  unfold rdef
  set F := F₁ t s L
  set G₀ := ((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L)
  set Q := IW t s (2 * t * L) Y / G t s (2 * t * L)
  set R' := Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      (-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y) / γt' t s
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) ha
  have hb0 : 0 ≤ b := le_trans (norm_nonneg _) hb
  have hd' : ‖Q - 1‖ ≤ d := by
    have hGn : 0 < ‖G t s (2 * t * L)‖ := norm_pos_iff.mpr hG
    have : Q - 1 = (IW t s (2 * t * L) Y - G t s (2 * t * L)) / G t s (2 * t * L) := by
      rw [sub_div, div_self hG]
    rw [this, norm_div, div_le_iff₀ hGn]
    exact hd
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) hd'
  have hQ : ‖Q‖ ≤ 1 + d := by
    have := norm_sub_norm_le Q 1
    rw [norm_one] at this
    linarith
  have hG₀ : ‖G₀‖ ≤ 1 + b := by
    have := norm_sub_norm_le G₀ 1
    rw [norm_one] at this
    linarith
  have h1 : ‖F * G₀ - 1‖ ≤ a * (1 + b) + b := by
    calc ‖F * G₀ - 1‖ = ‖(F - 1) * G₀ + (G₀ - 1)‖ := by ring_nf
      _ ≤ ‖(F - 1) * G₀‖ + ‖G₀ - 1‖ := norm_add_le _ _
      _ = ‖F - 1‖ * ‖G₀‖ + ‖G₀ - 1‖ := by rw [norm_mul]
      _ ≤ a * (1 + b) + b := by gcongr
  have h2 : ‖F * G₀ * Q - 1‖ ≤ (a * (1 + b) + b) * (1 + d) + d := by
    calc ‖F * G₀ * Q - 1‖ = ‖(F * G₀ - 1) * Q + (Q - 1)‖ := by ring_nf
      _ ≤ ‖(F * G₀ - 1) * Q‖ + ‖Q - 1‖ := norm_add_le _ _
      _ = ‖F * G₀ - 1‖ * ‖Q‖ + ‖Q - 1‖ := by rw [norm_mul]
      _ ≤ (a * (1 + b) + b) * (1 + d) + d := by gcongr
  calc ‖F * G₀ * Q - 1 + R'‖ ≤ ‖F * G₀ * Q - 1‖ + ‖R'‖ := norm_add_le _ _
    _ ≤ (a * (1 + b) + b) * (1 + d) + d + e := by gcongr

end Soma.Holonics.RH.EventDefect
