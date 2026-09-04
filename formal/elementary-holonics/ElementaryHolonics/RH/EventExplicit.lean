import Mathlib
import ElementaryHolonics.RH.EventHorizontal

/-!
# RT3 (iii-l): the relative defect, explicitly

Under the side conditions of the window through the saddle, `‖r‖ ≤ (a(1+b) + b)(1+d) + d + e`
with the four pieces written out.
-/

noncomputable section

namespace Soma.Holonics.RH.EventExplicit

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
open Soma.Holonics.RH.EventDefect
open Soma.Holonics.RH.EventHorizontal

/-- The window-defect bound `β₃`. -/
def β₃ (t : ℝ) (s : ℂ) (h : ℝ) : ℝ :=
  2 * Real.exp (8 * t) *
    ((1608 * h ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) * √(π / (3 / (32 * t))) +
      1608 / ‖s‖ ^ 2 * (7 * (3 / (32 * t)) ^ (-(3 / 2 : ℝ)) * √(π / (3 * (3 / (32 * t)) / 4))))

/-- The Gaussian-tail bound `β₄`. -/
def β₄ (t Y : ℝ) : ℝ :=
  2 * Real.exp (8 * t) * √(2 * π / (3 / (32 * t))) * Real.exp (-((3 / (32 * t)) / 2) * Y ^ 2)

/-- The `R'` bound `e`. -/
def epiece (t X : ℝ) (s : ℂ) (L Y : ℝ) : ℝ :=
  (2 * MH t X (2 * t * L) Y s.im (2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) *
      (X + 2 * t * L + 2) +
    2 * (Real.exp ((2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) ^ 2 / (4 * t)) /
      (2 * π)) * (1 + |s.im| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t)))) *
    (√(4 * π * t))⁻¹ / γlow t X s

/-- **The relative defect, explicitly.** -/
theorem norm_rdef_le_explicit {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    (hs2π : 2 * π ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) (hstrip : 4 * |s.re| ≤ s.im) (hy2' : 2 ≤ s.im)
    {L : ℝ} (hL : 0 ≤ L) {Y : ℝ} (hY : 0 < Y) (hY2 : 2 * t * π ≤ Y)
    (hsec : X + 2 * t * L + 2 ≤ s.im - Y) (hy2 : 2 ≤ s.im - Y)
    (hζY : 2 * t * L + Y ≤ ‖s‖ / 8)
    (hsmall : 402 * (2 * t * L + Y) ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) ≤ 1)
    (hq : ‖q s (2 * t * L)‖ ≤ 1) (hq2 : 2 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 1)
    (hF : (6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖ ≤ 1) :
    ‖rdef t s L Y‖ ≤
      ((2 * ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖)) *
          (1 + (36 * t / ‖s‖ + 4 * t * ‖q s (2 * t * L)‖ ^ 2)) +
          (36 * t / ‖s‖ + 4 * t * ‖q s (2 * t * L)‖ ^ 2)) *
        (1 + (β₃ t s (2 * t * L) + β₄ t Y) /
          (√(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2)))) +
      (β₃ t s (2 * t * L) + β₄ t Y) /
        (√(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2))) +
      epiece t X s L Y := by
  have hs : 2 ≤ ‖s‖ := by linarith [Real.pi_gt_three]
  have hs0 : 0 < ‖s‖ := by linarith
  set h : ℝ := 2 * t * L with hh
  have hh0 : 0 ≤ h := by positivity
  have hY0 : 0 ≤ Y := hY.le
  have hYt : t * π ≤ Y := by nlinarith [Real.pi_pos]
  have hy : Y < s.im := by linarith
  have hs_ne : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs
    linarith
  have hs_ne1 : s ≠ 1 := by
    intro h1
    rw [h1, Complex.one_im] at hy2'
    linarith
  have hg : g s ≠ 0 := g_ne_zero hs_ne hs_ne1
  -- the Gaussian
  set g₀ : ℝ := √(2 * π * t) * Real.exp (-(2 * t * ‖q s h‖ ^ 2)) with hg₀
  have hg₀pos : 0 < g₀ := by positivity
  have hGge : g₀ ≤ ‖G t s h‖ := norm_G_ge ht hs hst h
  have hG : G t s h ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hGge
    linarith
  have hδ : ‖δ t s‖ ≤ 1 / 2 := by
    refine (norm_δ_le ht hs).trans ?_
    rw [div_le_iff₀ hs0]
    linarith
  -- the four pieces
  have ha := norm_F₁_sub_one_le ht.le hs hL hF
  have hb := norm_sqrt_G_sub_one_le ht hs hst hδ hq2
  have hζ : ∀ v : ℝ, |v| ≤ Y → ‖(h : ℂ) + Complex.I * v‖ ≤ ‖s‖ / 8 := by
    intro v hv
    calc ‖(h : ℂ) + Complex.I * v‖ ≤ ‖(h : ℂ)‖ + ‖Complex.I * v‖ := norm_add_le _ _
      _ = h + |v| := by simp [abs_of_nonneg hh0]
      _ ≤ h + Y := by linarith
      _ ≤ ‖s‖ / 8 := hζY
  have hgood : ∀ v : ℝ, |v| ≤ Y → GoodSeg s (h + Complex.I * v) :=
    fun v hv => goodSeg_of_im hstrip hy2' (hζ v hv)
  have hβ₃ := norm_window_defect_le ht hs hst hh0 hq hY0 hgood hζ hsmall
  have hβ₄ := norm_G_sub_window_le ht hs hst hq hY0
  have hd : ‖IW t s h Y - G t s h‖ ≤ ((β₃ t s h + β₄ t Y) / g₀) * ‖G t s h‖ := by
    rw [IW_sub_G hg h hY0 hy]
    have h1 : ‖IW t s h Y - G t s h‖ ≤ β₃ t s h + β₄ t Y := by
      rw [IW_sub_G hg h hY0 hy]
      refine (norm_sub_le _ _).trans ?_
      unfold β₃ β₄
      exact add_le_add hβ₃ hβ₄
    rw [← IW_sub_G hg h hY0 hy]
    have hβ0 : 0 ≤ β₃ t s h + β₄ t Y := le_trans (norm_nonneg _) h1
    calc ‖IW t s h Y - G t s h‖ ≤ β₃ t s h + β₄ t Y := h1
      _ = ((β₃ t s h + β₄ t Y) / g₀) * g₀ := by field_simp
      _ ≤ ((β₃ t s h + β₄ t Y) / g₀) * ‖G t s h‖ := by gcongr
  have he := norm_Rpiece_le ht hX0 hX hs2π hL hY2 hsec hy2
  have := norm_rdef_le (t := t) (s := s) (L := L) (Y := Y) hG ha hb hd he
  unfold epiece
  exact this

end Soma.Holonics.RH.EventExplicit
