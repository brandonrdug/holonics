import Mathlib
import ElementaryHolonics.RH.EventMainRange

/-!
# RT3 (iii-e): the medium range, in absolute value

For `L = log |n|` up to `y^{7/12}` the same decomposition holds, but `F₁` is no longer close
to `1`; we bound the event in absolute value by
`12 ‖γ_t(s)‖ e^{−Re s · L} e^{−tL²/2}`, with the half of the Gaussian decay kept.
-/

noncomputable section

namespace Soma.Holonics.RH.EventMedium

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventGaussian
open Soma.Holonics.RH.EventWindow
open Soma.Holonics.RH.EventTail
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventHorizontal
open Soma.Holonics.RH.EventAssembly
open Soma.Holonics.RH.EventDefect
open Soma.Holonics.RH.EventExplicit
open Soma.Holonics.RH.EventMainRange

/-! ## A general vanishing lemma -/

/-- `exp(−a wᴺ + p(w)) → 0` when `p(w) ≤ C w^{N−1}` for `w ≥ 1`. -/
theorem tendsto_exp_neg_pow_add {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 1 ≤ N) {p : ℝ → ℝ} {C : ℝ}
    (hp : ∀ w, 1 ≤ w → p w ≤ C * w ^ (N - 1)) :
    Tendsto (fun w => Real.exp (-a * w ^ N + p w)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun w : ℝ => -a * w + C) atTop atBot := by
    have h1 : Tendsto (fun w : ℝ => -a * w) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr ha) tendsto_id
    exact h1.atBot_add tendsto_const_nhds
  have h1 : Tendsto (fun w : ℝ => w ^ (N - 1) * (-a * w + C)) atTop atBot := by
    rcases Nat.eq_zero_or_pos (N - 1) with h0 | hpos
    · simpa [h0] using hlin
    · exact Tendsto.atTop_mul_atBot₀ (tendsto_pow_atTop (by omega)) hlin
  have h2 : Tendsto (fun w => -a * w ^ N + p w) atTop atBot := by
    refine tendsto_atBot_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop 1] with w hw
    have := hp w hw
    have hwN : w ^ N = w ^ (N - 1) * w := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hwN]
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ w) (N - 1)]
  exact Real.tendsto_exp_atBot.comp h2

/-- A monomial of degree `≤ N` is at most `|A| w^N` for `w ≥ 1`. -/
theorem monomial_le {w : ℝ} (hw : 1 ≤ w) (A : ℝ) {k N : ℕ} (hk : k ≤ N) :
    A * w ^ k ≤ |A| * w ^ N := by
  have h1 : w ^ k ≤ w ^ N := pow_le_pow_right₀ hw hk
  have h2 : A * w ^ k ≤ |A| * w ^ k :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (pow_nonneg (by linarith) k)
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg A))

/-! ## The absolute bound on `1 + r` -/

theorem norm_F₁_le {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 2 ≤ ‖s‖) {L : ℝ} (hL : 0 ≤ L) :
    ‖F₁ t s L‖ ≤ Real.exp ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖) := by
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
  calc ‖Complex.exp ((2 : ℂ) * t * L * ε₁ s + 2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s)‖
      = Real.exp ((2 : ℂ) * t * L * ε₁ s + 2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s).re :=
        Complex.norm_exp _
    _ ≤ Real.exp ‖(2 : ℂ) * t * L * ε₁ s + 2 * (t : ℂ) ^ 2 * (L : ℂ) ^ 2 * ℓ' s‖ :=
        Real.exp_le_exp.mpr (Complex.re_le_norm _)
    _ ≤ Real.exp ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖) := Real.exp_le_exp.mpr hE

theorem norm_one_add_rdef_le {t : ℝ} {s : ℂ} {L Y : ℝ} {b d e : ℝ}
    (hG : G t s (2 * t * L) ≠ 0)
    (hb : ‖((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L) - 1‖ ≤ b)
    (hd : ‖IW t s (2 * t * L) Y - G t s (2 * t * L)‖ ≤ d * ‖G t s (2 * t * L)‖)
    (he : ‖Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      (-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y) / γt' t s‖ ≤ e) :
    ‖1 + rdef t s L Y‖ ≤ ‖F₁ t s L‖ * (1 + b) * (1 + d) + e := by
  unfold rdef
  set F := F₁ t s L
  set G₀ := ((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L)
  set Q := IW t s (2 * t * L) Y / G t s (2 * t * L)
  set R' := Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      (-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y) / γt' t s
  have hG0 : 0 < ‖G t s (2 * t * L)‖ := norm_pos_iff.mpr hG
  have hG₀ : ‖G₀‖ ≤ 1 + b := by
    calc ‖G₀‖ = ‖(G₀ - 1) + 1‖ := by ring_nf
      _ ≤ ‖G₀ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ b + 1 := by rw [norm_one]; gcongr
      _ = 1 + b := by ring
  have hQ : ‖Q‖ ≤ 1 + d := by
    have hIW : ‖IW t s (2 * t * L) Y‖ ≤ (1 + d) * ‖G t s (2 * t * L)‖ := by
      calc ‖IW t s (2 * t * L) Y‖
          = ‖(IW t s (2 * t * L) Y - G t s (2 * t * L)) + G t s (2 * t * L)‖ := by ring_nf
        _ ≤ ‖IW t s (2 * t * L) Y - G t s (2 * t * L)‖ + ‖G t s (2 * t * L)‖ := norm_add_le _ _
        _ ≤ d * ‖G t s (2 * t * L)‖ + ‖G t s (2 * t * L)‖ := by gcongr
        _ = (1 + d) * ‖G t s (2 * t * L)‖ := by ring
    calc ‖Q‖ = ‖IW t s (2 * t * L) Y‖ / ‖G t s (2 * t * L)‖ := norm_div _ _
      _ ≤ (1 + d) * ‖G t s (2 * t * L)‖ / ‖G t s (2 * t * L)‖ := by gcongr
      _ = 1 + d := by field_simp
  have hb0 : 0 ≤ b := le_trans (norm_nonneg _) hb
  have hd0 : 0 ≤ d := by
    by_contra hneg
    push_neg at hneg
    have : d * ‖G t s (2 * t * L)‖ < 0 := mul_neg_of_neg_of_pos hneg hG0
    linarith [norm_nonneg (IW t s (2 * t * L) Y - G t s (2 * t * L))]
  calc ‖1 + (F * G₀ * Q - 1 + R')‖ = ‖F * G₀ * Q + R'‖ := by ring_nf
    _ ≤ ‖F * G₀ * Q‖ + ‖R'‖ := norm_add_le _ _
    _ = ‖F‖ * ‖G₀‖ * ‖Q‖ + ‖R'‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖F‖ * (1 + b) * (1 + d) + e := by gcongr

/-- **The medium-range event bound, abstractly.** With `b, d, e ≤ 1` and `6tL ≤ ‖s‖`,
`‖event‖ ≤ 12 ‖γ_t(s)‖ e^{−Re s · L} e^{−tL²/2}`. -/
theorem norm_event_le_medium {t : ℝ} (ht : 0 < t) {s : ℂ} (hg : g s ≠ 0) (hs : 2 ≤ ‖s‖)
    (hst : 12 * t ≤ ‖s‖) {n : ℤ} (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y) (hy : Y < s.im)
    (hL6 : 6 * t * Real.log |(n : ℝ)| ≤ ‖s‖)
    (hone : ‖1 + rdef t s (Real.log |(n : ℝ)|) Y‖ ≤ ‖F₁ t s (Real.log |(n : ℝ)|)‖ * 4 + 1) :
    ‖∫ v : ℝ, flowedTerm t (J t s) n v‖ ≤
      12 * ‖γt' t s‖ * Real.exp (-s.re * Real.log |(n : ℝ)|) *
        Real.exp (-(t / 2) * Real.log |(n : ℝ)| ^ 2) := by
  set L : ℝ := Real.log |(n : ℝ)| with hLdef
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    have := Int.one_le_abs hn
    exact_mod_cast this
  have hs0 : 0 < ‖s‖ := by linarith
  rw [event_eq_main_mul ht hg hs hst hn hY hy]
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖Complex.exp (-s * ((L : ℝ) : ℂ))‖ = Real.exp (-s.re * L) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h2 : ‖Complex.exp (-(t : ℂ) * ((L : ℝ) : ℂ) ^ 2)‖ = Real.exp (-t * L ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, sq]
  rw [h1, h2]
  have hF : ‖F₁ t s L‖ ≤ Real.exp (1 + t / 2 * L ^ 2) := by
    refine (norm_F₁_le ht.le hs hL0).trans (Real.exp_le_exp.mpr ?_)
    rw [div_le_iff₀ hs0]
    have e1 : 6 * t * L ≤ ‖s‖ := hL6
    have e2 : 6 * t ^ 2 * L ^ 2 ≤ t / 2 * L ^ 2 * ‖s‖ := by
      have : 12 * t * (t * L ^ 2) ≤ ‖s‖ * (t * L ^ 2) :=
        mul_le_mul_of_nonneg_right hst (by positivity)
      nlinarith
    nlinarith
  have hone' : ‖1 + rdef t s L Y‖ ≤ 12 * Real.exp (t / 2 * L ^ 2) := by
    refine hone.trans ?_
    have hE := Real.exp_pos (t / 2 * L ^ 2)
    have hE1 : 1 ≤ Real.exp (t / 2 * L ^ 2) := Real.one_le_exp (by positivity)
    have he : Real.exp 1 ≤ 11 / 4 := by
      have := Real.exp_one_lt_d9
      linarith
    calc ‖F₁ t s L‖ * 4 + 1 ≤ Real.exp (1 + t / 2 * L ^ 2) * 4 + 1 := by gcongr
      _ = Real.exp 1 * Real.exp (t / 2 * L ^ 2) * 4 + 1 := by rw [Real.exp_add]
      _ ≤ 11 / 4 * Real.exp (t / 2 * L ^ 2) * 4 + Real.exp (t / 2 * L ^ 2) := by gcongr
      _ = 12 * Real.exp (t / 2 * L ^ 2) := by ring
  calc ‖γt' t s‖ * Real.exp (-s.re * L) * Real.exp (-t * L ^ 2) * ‖1 + rdef t s L Y‖
      ≤ ‖γt' t s‖ * Real.exp (-s.re * L) * Real.exp (-t * L ^ 2) *
        (12 * Real.exp (t / 2 * L ^ 2)) := by gcongr
    _ = 12 * ‖γt' t s‖ * Real.exp (-s.re * L) * (Real.exp (-t * L ^ 2) *
        Real.exp (t / 2 * L ^ 2)) := by ring
    _ = 12 * ‖γt' t s‖ * Real.exp (-s.re * L) * Real.exp (-(t / 2) * L ^ 2) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-! ## The explicit form on the medium range -/

theorem norm_one_add_rdef_le_explicit {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ}
    (hX : |s.re| ≤ X) (hs2π : 2 * π ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) (hstrip : 4 * |s.re| ≤ s.im)
    (hy2' : 2 ≤ s.im) {L : ℝ} (hL : 0 ≤ L) {Y : ℝ} (hY : 0 < Y) (hY2 : 2 * t * π ≤ Y)
    (hsec : X + 2 * t * L + 2 ≤ s.im - Y) (hy2 : 2 ≤ s.im - Y)
    (hζY : 2 * t * L + Y ≤ ‖s‖ / 8)
    (hsmall : 402 * (2 * t * L + Y) ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) ≤ 1)
    (hq : ‖q s (2 * t * L)‖ ≤ 1) (hq2 : 2 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 1) :
    ‖1 + rdef t s L Y‖ ≤
      ‖F₁ t s L‖ * (1 + (36 * t / ‖s‖ + 4 * t * ‖q s (2 * t * L)‖ ^ 2)) *
        (1 + (β₃ t s (2 * t * L) + β₄ t Y) /
          (√(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2)))) +
      epiece t X s L Y := by
  have hs : 2 ≤ ‖s‖ := by linarith [Real.pi_gt_three]
  have hs0 : 0 < ‖s‖ := by linarith
  set h : ℝ := 2 * t * L with hh
  have hh0 : 0 ≤ h := by positivity
  have hY0 : 0 ≤ Y := hY.le
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
    have h1 : ‖IW t s h Y - G t s h‖ ≤ β₃ t s h + β₄ t Y := by
      rw [IW_sub_G hg h hY0 hy]
      refine (norm_sub_le _ _).trans ?_
      unfold β₃ β₄
      exact add_le_add hβ₃ hβ₄
    have hβ0 : 0 ≤ β₃ t s h + β₄ t Y := le_trans (norm_nonneg _) h1
    calc ‖IW t s h Y - G t s h‖ ≤ β₃ t s h + β₄ t Y := h1
      _ = ((β₃ t s h + β₄ t Y) / g₀) * g₀ := by field_simp
      _ ≤ ((β₃ t s h + β₄ t Y) / g₀) * ‖G t s h‖ := by gcongr
  have he := norm_Rpiece_le ht hX0 hX hs2π hL hY2 hsec hy2
  have := norm_one_add_rdef_le (t := t) (s := s) (L := L) (Y := Y) hG hb hd he
  unfold epiece
  exact this

/-! ## The majorants in `w`, with `y = w¹²`, `Y = w⁸/20`, `L ≤ w⁷` -/

/-- `c₁' = 2X + 2 + 22t` majorizes `ξ₁ / w⁷` on the medium range. -/
def c₁' (t X : ℝ) : ℝ := 2 * X + 2 + 22 * t

def Dmed (t w : ℝ) : ℝ := Real.exp 1 / √(2 * π * t) * (β₃maj t w + β₄maj t (w ^ 4))
def Mmed (t X w : ℝ) : ℝ :=
  Real.exp ((c₁' t X ^ 2 * w ^ 14 - w ^ 16 / 1600) / (4 * t)) *
    (Real.exp (π / 4) * (√(2 * π) / 2 * (cZ t X * w ^ 12) ^ 2 *
      (cZ t X * w ^ 12) ^ ((cξ t X * w ^ 7 + 1) / 2) * (π * Real.exp 1) ^ (cξ t X * w ^ 7 / 2)))
def Tmed (t X w : ℝ) : ℝ :=
  2 * (Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) / (2 * π)) * (1 + w ^ 12 + 4 * √t) *
    √(64 * π * t) * Real.exp (-((w ^ 8 / 20) ^ 2 / (64 * t)))
def Emed (t X w : ℝ) : ℝ :=
  (2 * Mmed t X w * (cξ t X * w ^ 7) + Tmed t X w) * (√(4 * π * t))⁻¹ * Γmaj t X (w ^ 4)

theorem log_norm_s_le_med {s : ℂ} {w : ℝ} (hw : 1 ≤ w) (hs1 : 1 ≤ ‖s‖)
    (hs2 : ‖s‖ ≤ 2 * w ^ 12) : Real.log ‖s‖ ≤ 12 * w := by
  have hw0 : 0 < w := by linarith
  calc Real.log ‖s‖ ≤ Real.log (2 * w ^ 12) := Real.log_le_log (by linarith) hs2
    _ = Real.log 2 + 12 * Real.log w := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
    _ ≤ 1 + 12 * (w - 1) := by
        have := Real.log_two_lt_d9
        have := Real.log_le_sub_one_of_pos hw0
        nlinarith
    _ ≤ 12 * w := by linarith

theorem ξ₁_le_med {t X : ℝ} (ht : 0 ≤ t) (hX0 : 0 ≤ X) {s : ℂ} {w L : ℝ} (hw : 1 ≤ w)
    (hL : 0 ≤ L) (hLw : L ≤ w ^ 7) (hs1 : 1 ≤ ‖s‖) (hs2 : ‖s‖ ≤ 2 * w ^ 12) :
    2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6) ≤ c₁' t X * w ^ 7 := by
  have hw7 : 1 ≤ w ^ 7 := one_le_pow₀ hw
  have hw1 : w ≤ w ^ 7 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 7 := pow_le_pow_right₀ hw (by norm_num)
  have hlog := log_norm_s_le_med hw hs1 hs2
  unfold c₁'
  have e1 : t * (Real.log ‖s‖ + 6) ≤ t * (12 * w + 6) := by gcongr
  nlinarith [mul_le_mul_of_nonneg_left hLw ht, mul_le_mul_of_nonneg_left hw1 ht,
    mul_nonneg ht (sub_nonneg.mpr hw7), mul_nonneg hX0 (sub_nonneg.mpr hw7)]

theorem ξ_le_med {t X : ℝ} (ht : 0 ≤ t) (hX0 : 0 ≤ X) {w L : ℝ} (hw : 1 ≤ w) (hL : 0 ≤ L)
    (hLw : L ≤ w ^ 7) : X + 2 * t * L + 2 ≤ cξ t X * w ^ 7 := by
  have hw7 : 1 ≤ w ^ 7 := one_le_pow₀ hw
  unfold cξ
  nlinarith [mul_le_mul_of_nonneg_left hLw ht, mul_nonneg ht (sub_nonneg.mpr hw7),
    mul_nonneg hX0 (sub_nonneg.mpr hw7)]

theorem Z_le_med {t X : ℝ} (ht : 0 ≤ t) (hX0 : 0 ≤ X) {w L : ℝ} (hw : 1 ≤ w) (hL : 0 ≤ L)
    (hLw : L ≤ w ^ 7) : X + 2 * t * L + 2 + w ^ 12 + w ^ 8 / 20 ≤ cZ t X * w ^ 12 := by
  have hξ := ξ_le_med ht hX0 hw hL hLw
  have hw0 : 0 ≤ w := by linarith
  have h7 : w ^ 7 ≤ w ^ 12 := pow_le_pow_right₀ hw (by norm_num)
  have h8 : w ^ 8 ≤ w ^ 12 := pow_le_pow_right₀ hw (by norm_num)
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have := mul_le_mul_of_nonneg_left h7 hcξ
  unfold cZ
  nlinarith

theorem β₃_le_of {t : ℝ} (ht : 0 < t) {s : ℂ} {h w : ℝ} (hw : 0 < w)
    (hb : 1608 * h ^ 3 / ‖s‖ ^ 2 ≤ 12864 * t ^ 3 / w)
    (hc : 2 * π / (3 * ‖s‖) ≤ (2 * π / 3) / w) (hd : 1608 / ‖s‖ ^ 2 ≤ 1608 / w) :
    β₃ t s h ≤ β₃maj t w := by
  unfold β₃ β₃maj
  have hI₀ := I₀_nonneg t
  have hI₃ := I₃_nonneg ht
  have hI₀' : √(π / (3 / (32 * t))) = I₀ t := rfl
  have hI₃' : 7 * (3 / (32 * t)) ^ (-(3 / 2 : ℝ)) * √(π / (3 * (3 / (32 * t)) / 4)) = I₃ t := rfl
  rw [hI₀', hI₃']
  calc 2 * Real.exp (8 * t) * ((1608 * h ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) * I₀ t +
        1608 / ‖s‖ ^ 2 * I₃ t)
      ≤ 2 * Real.exp (8 * t) * ((12864 * t ^ 3 / w + (2 * π / 3) / w) * I₀ t + 1608 / w * I₃ t) := by
        gcongr
    _ = 2 * Real.exp (8 * t) * ((12864 * t ^ 3 + 2 * π / 3) * I₀ t + 1608 * I₃ t) / w := by
        field_simp
        first | done | ring

theorem d_le_of {t : ℝ} (ht : 0 < t) {s : ℂ} {h Y B₃ B₄ : ℝ}
    (hq2 : 2 * t * ‖q s h‖ ^ 2 ≤ 1) (hβ₃ : β₃ t s h ≤ B₃) (hβ₄ : β₄ t Y ≤ B₄)
    (hB₃ : 0 ≤ B₃) (hB₄ : 0 ≤ B₄) :
    (β₃ t s h + β₄ t Y) / (√(2 * π * t) * Real.exp (-(2 * t * ‖q s h‖ ^ 2))) ≤
      Real.exp 1 / √(2 * π * t) * (B₃ + B₄) := by
  have hden : √(2 * π * t) * Real.exp (-1) ≤
      √(2 * π * t) * Real.exp (-(2 * t * ‖q s h‖ ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact Real.exp_le_exp.mpr (by linarith)
  have hden0 : 0 < √(2 * π * t) * Real.exp (-1) := by positivity
  calc (β₃ t s h + β₄ t Y) / (√(2 * π * t) * Real.exp (-(2 * t * ‖q s h‖ ^ 2)))
      ≤ (B₃ + B₄) / (√(2 * π * t) * Real.exp (-1)) := by
        apply div_le_div₀ (by positivity) (add_le_add hβ₃ hβ₄) hden0 hden
    _ = Real.exp 1 / √(2 * π * t) * (B₃ + B₄) := by
        rw [Real.exp_neg]
        field_simp

/-- The `d`-piece on the medium range. -/
theorem d_le_Dmed {t : ℝ} (ht : 0 < t) {s : ℂ} {w L : ℝ} (hw : 1 ≤ w) (hL : 0 ≤ L)
    (hLw : L ≤ w ^ 7) (hsu : w ^ 12 ≤ ‖s‖) (hq2 : 2 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 1) :
    (β₃ t s (2 * t * L) + β₄ t (w ^ 8 / 20)) /
      (√(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2))) ≤ Dmed t w := by
  have hw0 : 0 < w := by linarith
  have hw12 : 1 ≤ w ^ 12 := one_le_pow₀ hw
  have hs0 : 0 < ‖s‖ := by linarith
  have hw1_3 : w ≤ w ^ 3 := u_le_cube hw
  have hw3_24 : w ^ 3 ≤ w ^ 24 := pow_le_pow_right₀ hw (by norm_num)
  have hs24 : w ^ 24 ≤ ‖s‖ ^ 2 := by
    calc w ^ 24 = (w ^ 12) ^ 2 := by ring
      _ ≤ ‖s‖ ^ 2 := pow_le_pow_left₀ (by positivity) hsu 2
  have hβ₃ : β₃ t s (2 * t * L) ≤ β₃maj t w := by
    apply β₃_le_of ht hw0
    · have e1 : (2 * t * L) ^ 3 ≤ 8 * t ^ 3 * w ^ 21 := by
        have := pow_le_pow_left₀ hL hLw 3
        calc (2 * t * L) ^ 3 = 8 * t ^ 3 * L ^ 3 := by ring
          _ ≤ 8 * t ^ 3 * (w ^ 7) ^ 3 := by gcongr
          _ = 8 * t ^ 3 * w ^ 21 := by ring
      calc 1608 * (2 * t * L) ^ 3 / ‖s‖ ^ 2 ≤ 1608 * (8 * t ^ 3 * w ^ 21) / w ^ 24 := by
            gcongr
        _ = 12864 * t ^ 3 / w ^ 3 := by
            field_simp
            first | done | ring
        _ ≤ 12864 * t ^ 3 / w := by
            apply div_le_div_of_nonneg_left (by positivity) hw0 hw1_3
    · have : (2 * π / 3) / w = 2 * π / (3 * w) := by field_simp
      rw [this]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : w ≤ w ^ 12 := hw1_3.trans (pow_le_pow_right₀ hw (by norm_num))
      linarith
    · apply div_le_div_of_nonneg_left (by norm_num) hw0
      linarith
  have hβ₄ : β₄ t (w ^ 8 / 20) = β₄maj t (w ^ 4) := by
    unfold β₄ β₄maj
    congr 2
    · unfold c₃
      ring
  have hI₀ := I₀_nonneg t
  have hI₃ := I₃_nonneg ht
  unfold Dmed
  apply d_le_of ht hq2 hβ₃ hβ₄.le
  · unfold β₃maj; positivity
  · unfold β₄maj; positivity

/-! ## The `e`-piece on the medium range -/

theorem MH_le_Mmed {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {w L ξ₁ : ℝ} (hw : 1 ≤ w)
    (hL : 0 ≤ L) (hLw : L ≤ w ^ 7) (hξ₁0 : 0 ≤ ξ₁) (hξ₁ : ξ₁ ≤ c₁' t X * w ^ 7)
    (hY2 : 2 * t * π ≤ w ^ 8 / 20) :
    MH t X (2 * t * L) (w ^ 8 / 20) (w ^ 12) ξ₁ ≤ Mmed t X w := by
  have hw0 : 0 < w := by linarith
  have hZ := Z_le_med ht.le hX0 hw hL hLw
  have hξ := ξ_le_med ht.le hX0 hw hL hLw
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hZ0 : 0 ≤ X + 2 * t * L + 2 + w ^ 12 + w ^ 8 / 20 := by positivity
  have hw12 : 1 ≤ w ^ 12 := one_le_pow₀ hw
  have hcZ1 : 1 ≤ cZ t X * w ^ 12 := by
    unfold cZ
    nlinarith
  unfold MH Mmed
  have hexp : ξ₁ ^ 2 - (w ^ 8 / 20 - t * π) ^ 2 ≤ c₁' t X ^ 2 * w ^ 14 - w ^ 16 / 1600 := by
    have e1 : ξ₁ ^ 2 ≤ (c₁' t X * w ^ 7) ^ 2 := pow_le_pow_left₀ hξ₁0 hξ₁ 2
    have e2 : (w ^ 8 / 40) ^ 2 ≤ (w ^ 8 / 20 - t * π) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [Real.pi_pos]
    nlinarith
  have hπe : 1 ≤ π * Real.exp 1 := by nlinarith [Real.pi_gt_three, Real.add_one_le_exp 1]
  have e3 : (X + 2 * t * L + 2 + w ^ 12 + w ^ 8 / 20) ^ ((X + 2 * t * L + 2 + 1) / 2) ≤
      (cZ t X * w ^ 12) ^ ((cξ t X * w ^ 7 + 1) / 2) :=
    (Real.rpow_le_rpow hZ0 hZ (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le hcZ1 (by linarith))
  have e4 : (π * Real.exp 1) ^ ((X + 2 * t * L + 2) / 2) ≤
      (π * Real.exp 1) ^ (cξ t X * w ^ 7 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hπe (by linarith)
  have e5 : (X + 2 * t * L + 2 + w ^ 12 + w ^ 8 / 20) ^ 2 ≤ (cZ t X * w ^ 12) ^ 2 :=
    pow_le_pow_left₀ hZ0 hZ 2
  apply mul_le_mul (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hexp (by positivity)))
    _ (by positivity) (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left e5 (by positivity)) e3
    (by positivity) (by positivity)) e4 (by positivity) (by positivity)

theorem T_le_Tmed {t X : ℝ} (ht : 0 < t) {w ξ₁ : ℝ} (hw : 1 ≤ w)
    (hξ₁0 : 0 ≤ ξ₁) (hξ₁ : ξ₁ ≤ c₁' t X * w ^ 7) :
    2 * (Real.exp (ξ₁ ^ 2 / (4 * t)) / (2 * π)) * (1 + |w ^ 12| + 4 * √t) * √(64 * π * t) *
      Real.exp (-((w ^ 8 / 20) ^ 2 / (64 * t))) ≤ Tmed t X w := by
  have hw0 : 0 < w := by linarith
  unfold Tmed
  rw [abs_of_nonneg (by positivity)]
  have e1 : Real.exp (ξ₁ ^ 2 / (4 * t)) ≤ Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := pow_le_pow_left₀ hξ₁0 hξ₁ 2
    nlinarith
  gcongr

theorem Mmed_nonneg {t X w : ℝ} (hcZ : 0 ≤ cZ t X * w ^ 12) : 0 ≤ Mmed t X w := by
  unfold Mmed
  apply mul_nonneg (Real.exp_pos _).le
  apply mul_nonneg (Real.exp_pos _).le
  apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (Real.rpow_nonneg hcZ _)) (Real.rpow_nonneg (by positivity) _)

theorem Tmed_nonneg {t X w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) : 0 ≤ Tmed t X w := by
  unfold Tmed; positivity

theorem Γmaj_nonneg {t X u : ℝ} (hu : 0 ≤ u) : 0 ≤ Γmaj t X u := by
  unfold Γmaj
  have := cg_pos X
  have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * u ^ 3) ((X + 1) / 2)
  positivity

theorem epiece_le_Emed {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    {w : ℝ} (hw : 1 ≤ w) (hy : s.im = w ^ 12) (hXw : X ≤ w ^ 12) {L : ℝ} (hL : 0 ≤ L)
    (hLw : L ≤ w ^ 7) (hY2 : 2 * t * π ≤ w ^ 8 / 20) :
    epiece t X s L (w ^ 8 / 20) ≤ Emed t X w := by
  have hw0 : 0 < w := by linarith
  have hw4 : 1 ≤ w ^ 4 := one_le_pow₀ hw
  have hy' : s.im = (w ^ 4) ^ 3 := by rw [hy]; ring
  have hXw' : X ≤ (w ^ 4) ^ 3 := by rw [show (w ^ 4) ^ 3 = w ^ 12 by ring]; exact hXw
  have hsu : w ^ 12 ≤ ‖s‖ := by
    have := norm_s_ge hy' (by positivity)
    rw [show (w ^ 4) ^ 3 = w ^ 12 by ring] at this
    exact this
  have hs2u : ‖s‖ ≤ 2 * (w ^ 4) ^ 3 := norm_s_le hX hy' hXw' (by positivity)
  have hs2u' : ‖s‖ ≤ 2 * w ^ 12 := by
    rw [show (w ^ 4) ^ 3 = w ^ 12 by ring] at hs2u
    exact hs2u
  have hw12 : 1 ≤ w ^ 12 := one_le_pow₀ hw
  have hs1 : 1 ≤ ‖s‖ := by linarith
  have hs0 : 0 < ‖s‖ := by linarith
  have hξ := ξ_le_med ht.le hX0 hw hL hLw
  have hξ₁ := ξ₁_le_med ht.le hX0 hw hL hLw hs1 hs2u'
  have hξ₁0 : 0 ≤ 2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6) := by
    have : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs1
    positivity
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hξ0 : 0 ≤ X + 2 * t * L + 2 := by positivity
  have hM := MH_le_Mmed ht hX0 hw hL hLw hξ₁0 hξ₁ hY2
  have hT := T_le_Tmed (X := X) ht hw hξ₁0 hξ₁
  have hΓ := inv_γlow_le_Γmaj (t := t) ht hX0 hw4 hs1 hs2u
  have hγpos : 0 < γlow t X s := γlow_pos hs0
  have hMH0 : 0 ≤ MH t X (2 * t * L) (w ^ 8 / 20) (w ^ 12)
      (2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) := MH_nonneg (by positivity)
  have hTm0 := Tmed_nonneg (X := X) ht hw0.le
  have hMm0 : 0 ≤ Mmed t X w := Mmed_nonneg (by unfold cZ cξ; positivity)
  have hT0 : 0 ≤ 2 * (Real.exp ((2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) ^ 2 /
      (4 * t)) / (2 * π)) * (1 + |w ^ 12| + 4 * √t) * √(64 * π * t) *
      Real.exp (-((w ^ 8 / 20) ^ 2 / (64 * t))) := by positivity
  unfold epiece
  rw [hy]
  rw [div_eq_mul_one_div]
  apply mul_le_mul (mul_le_mul_of_nonneg_right _ (by positivity)) hΓ (by positivity) (by positivity)
  exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hξ hξ0
    (by positivity)) hT

/-! ## Exponential domination and vanishing -/

theorem const_le_exp_two : Real.exp (π / 4) * (√(2 * π) / 2) ≤ Real.exp 2 := by
  have h1 : Real.exp (π / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [Real.pi_le_four])
  have h2 : √(2 * π) ≤ 3 := by
    calc √(2 * π) ≤ √9 := Real.sqrt_le_sqrt (by nlinarith [Real.pi_le_four])
      _ = 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h4 := Real.add_one_le_exp (1 : ℝ)
  have h5 := Real.exp_pos (1 : ℝ)
  have h6 := Real.exp_pos (π / 4)
  rw [h3]
  nlinarith [Real.sqrt_nonneg (2 * π)]

theorem log_cZ_pow_le {t X w : ℝ} (ht : 0 ≤ t) (hX0 : 0 ≤ X) (hw : 1 ≤ w) :
    Real.log (cZ t X * w ^ 12) ≤ (cZ t X + 12) * w := by
  have hw0 : 0 < w := by linarith
  have hcZ : 2 ≤ cZ t X := by unfold cZ cξ; linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < cZ t X)
  have := Real.log_le_sub_one_of_pos hw0
  push_cast
  nlinarith

/-- The lower-order part of the exponent majorizing `Mmed`. -/
def pM (t X w : ℝ) : ℝ :=
  c₁' t X ^ 2 / (4 * t) * w ^ 14 + (cZ t X + 12) * (cξ t X + 1) / 2 * w ^ 8 +
    2 * cξ t X * w ^ 7 + 2 * (cZ t X + 12) * w + 2

theorem Mmed_le_exp {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {w : ℝ} (hw : 1 ≤ w) :
    Mmed t X w ≤ Real.exp (-(1 / (6400 * t)) * w ^ 16 + pM t X w) := by
  have hw0 : 0 < w := by linarith
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hcZ : 2 ≤ cZ t X := by unfold cZ cξ; linarith
  have hw12 : 1 ≤ w ^ 12 := one_le_pow₀ hw
  have hw7 : 1 ≤ w ^ 7 := one_le_pow₀ hw
  have hb : 1 ≤ cZ t X * w ^ 12 := by nlinarith
  have hb0 : 0 < cZ t X * w ^ 12 := by linarith
  have hlogb := log_cZ_pow_le ht.le hX0 hw
  have hlogb0 : 0 ≤ Real.log (cZ t X * w ^ 12) := Real.log_nonneg hb
  have e1 : (cZ t X * w ^ 12) ^ ((cξ t X * w ^ 7 + 1) / 2) ≤
      Real.exp ((cZ t X + 12) * (cξ t X + 1) / 2 * w ^ 8) := by
    rw [Real.rpow_def_of_pos hb0]
    apply Real.exp_le_exp.mpr
    have h1 : cξ t X * w ^ 7 + 1 ≤ (cξ t X + 1) * w ^ 7 := by nlinarith
    calc Real.log (cZ t X * w ^ 12) * ((cξ t X * w ^ 7 + 1) / 2)
        ≤ ((cZ t X + 12) * w) * (((cξ t X + 1) * w ^ 7) / 2) := by gcongr
      _ = (cZ t X + 12) * (cξ t X + 1) / 2 * w ^ 8 := by ring
  have e2 : (cZ t X * w ^ 12) ^ 2 ≤ Real.exp (2 * (cZ t X + 12) * w) := by
    rw [← Real.exp_log (by positivity : 0 < (cZ t X * w ^ 12) ^ 2), Real.log_pow]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have e3 : (π * Real.exp 1) ^ (cξ t X * w ^ 7 / 2) ≤ Real.exp (2 * cξ t X * w ^ 7) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    have := Real.pi_le_four
    have : 0 ≤ cξ t X * w ^ 7 := by positivity
    nlinarith
  have e4 := const_le_exp_two
  have hB0 : 0 ≤ (cZ t X * w ^ 12) ^ ((cξ t X * w ^ 7 + 1) / 2) := Real.rpow_nonneg hb0.le _
  have hC0 : 0 ≤ (π * Real.exp 1) ^ (cξ t X * w ^ 7 / 2) := Real.rpow_nonneg (by positivity) _
  unfold Mmed
  calc Real.exp ((c₁' t X ^ 2 * w ^ 14 - w ^ 16 / 1600) / (4 * t)) *
        (Real.exp (π / 4) * (√(2 * π) / 2 * (cZ t X * w ^ 12) ^ 2 *
          (cZ t X * w ^ 12) ^ ((cξ t X * w ^ 7 + 1) / 2) * (π * Real.exp 1) ^ (cξ t X * w ^ 7 / 2)))
      = Real.exp ((c₁' t X ^ 2 * w ^ 14 - w ^ 16 / 1600) / (4 * t)) *
        ((Real.exp (π / 4) * (√(2 * π) / 2)) * ((cZ t X * w ^ 12) ^ 2 *
          (cZ t X * w ^ 12) ^ ((cξ t X * w ^ 7 + 1) / 2) *
          (π * Real.exp 1) ^ (cξ t X * w ^ 7 / 2))) := by ring
    _ ≤ Real.exp ((c₁' t X ^ 2 * w ^ 14 - w ^ 16 / 1600) / (4 * t)) *
        (Real.exp 2 * (Real.exp (2 * (cZ t X + 12) * w) *
          Real.exp ((cZ t X + 12) * (cξ t X + 1) / 2 * w ^ 8) *
          Real.exp (2 * cξ t X * w ^ 7))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul e4 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul (mul_le_mul e2 e1 hB0 (Real.exp_pos _).le) e3 hC0 (by positivity)
    _ = Real.exp (-(1 / (6400 * t)) * w ^ 16 + pM t X w) := by
        simp only [← Real.exp_add]
        congr 1
        unfold pM
        field_simp
        ring

/-- The lower-order part of the exponent majorizing `Tmed`. -/
def pT (t X w : ℝ) : ℝ := c₁' t X ^ 2 / (4 * t) * w ^ 14 + w ^ 12 + (4 * √t + √(64 * π * t))

theorem Tmed_le_exp {t X : ℝ} (ht : 0 < t) {w : ℝ} (hw : 1 ≤ w) :
    Tmed t X w ≤ Real.exp (-(1 / (25600 * t)) * w ^ 16 + pT t X w) := by
  have hw0 : 0 ≤ w := by linarith
  unfold Tmed
  have hE := Real.exp_pos (c₁' t X ^ 2 * w ^ 14 / (4 * t))
  have e1 : 2 * (Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) / (2 * π)) ≤
      Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) := by
    calc 2 * (Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) / (2 * π))
        = Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) / π := by
          field_simp
          first | done | ring
      _ ≤ Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) :=
          div_le_self hE.le (by linarith [Real.pi_gt_three])
  have e2 : 1 + w ^ 12 + 4 * √t ≤ Real.exp (w ^ 12 + 4 * √t) := by
    have := Real.add_one_le_exp (w ^ 12 + 4 * √t); linarith
  have e3 : √(64 * π * t) ≤ Real.exp (√(64 * π * t)) := by
    have := Real.add_one_le_exp (√(64 * π * t)); linarith
  calc 2 * (Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) / (2 * π)) * (1 + w ^ 12 + 4 * √t) *
        √(64 * π * t) * Real.exp (-((w ^ 8 / 20) ^ 2 / (64 * t)))
      ≤ Real.exp (c₁' t X ^ 2 * w ^ 14 / (4 * t)) * Real.exp (w ^ 12 + 4 * √t) *
        Real.exp (√(64 * π * t)) * Real.exp (-((w ^ 8 / 20) ^ 2 / (64 * t))) := by
        gcongr
    _ = Real.exp (-(1 / (25600 * t)) * w ^ 16 + pT t X w) := by
        simp only [← Real.exp_add]
        congr 1
        unfold pT
        field_simp
        ring

/-- The exponents majorizing the two parts of `Emed`. -/
def pEM (t X w : ℝ) : ℝ :=
  pM t X w + 2 * cξ t X * w ^ 7 + Real.log ((√(4 * π * t))⁻¹) + π * w ^ 12 +
    3 * (X + 1) / 2 * w ^ 4 + (Real.log (1 / cg X) + t * π ^ 2 / 4)
def pET (t X w : ℝ) : ℝ :=
  pT t X w + Real.log ((√(4 * π * t))⁻¹) + π * w ^ 12 +
    3 * (X + 1) / 2 * w ^ 4 + (Real.log (1 / cg X) + t * π ^ 2 / 4)

theorem Emed_le_exp {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {w : ℝ} (hw : 1 ≤ w) :
    Emed t X w ≤ Real.exp (-(1 / (6400 * t)) * w ^ 16 + pEM t X w) +
      Real.exp (-(1 / (25600 * t)) * w ^ 16 + pET t X w) := by
  have hw0 : 0 < w := by linarith
  have hw4 : 1 ≤ w ^ 4 := one_le_pow₀ hw
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hM := Mmed_le_exp ht hX0 hw
  have hT := Tmed_le_exp (X := X) ht hw
  have hΓ := Γmaj_le_exp (t := t) ht hX0 hw4
  have hk : (√(4 * π * t))⁻¹ = Real.exp (Real.log ((√(4 * π * t))⁻¹)) :=
    (Real.exp_log (by positivity)).symm
  have hcu : 2 * (cξ t X * w ^ 7) ≤ Real.exp (2 * cξ t X * w ^ 7) := by
    have := Real.add_one_le_exp (2 * cξ t X * w ^ 7); linarith
  have hMm0 : 0 ≤ Mmed t X w := Mmed_nonneg (by unfold cZ cξ; positivity)
  have hTm0 := Tmed_nonneg (X := X) ht hw0.le
  have hΓ0 : 0 ≤ Γmaj t X (w ^ 4) := Γmaj_nonneg (by positivity)
  unfold Emed
  calc (2 * Mmed t X w * (cξ t X * w ^ 7) + Tmed t X w) * (√(4 * π * t))⁻¹ * Γmaj t X (w ^ 4)
      = (Mmed t X w * (2 * (cξ t X * w ^ 7)) + Tmed t X w) * (√(4 * π * t))⁻¹ *
        Γmaj t X (w ^ 4) := by ring
    _ ≤ (Real.exp (-(1 / (6400 * t)) * w ^ 16 + pM t X w) * Real.exp (2 * cξ t X * w ^ 7) +
          Real.exp (-(1 / (25600 * t)) * w ^ 16 + pT t X w)) *
        Real.exp (Real.log ((√(4 * π * t))⁻¹)) *
        Real.exp (π * (w ^ 4) ^ 3 + 3 * (X + 1) / 2 * w ^ 4 +
          (Real.log (1 / cg X) + t * π ^ 2 / 4)) := by
        rw [← hk]
        apply mul_le_mul (mul_le_mul_of_nonneg_right _ (by positivity)) hΓ hΓ0 (by positivity)
        exact add_le_add (mul_le_mul hM hcu (by positivity) (Real.exp_pos _).le) hT
    _ = Real.exp (-(1 / (6400 * t)) * w ^ 16 + pEM t X w) +
        Real.exp (-(1 / (25600 * t)) * w ^ 16 + pET t X w) := by
        unfold pEM pET
        rw [add_mul, add_mul]
        simp only [← Real.exp_add]
        congr 1 <;> congr 1 <;> ring

theorem const_le_pow {w : ℝ} (hw : 1 ≤ w) (A : ℝ) (N : ℕ) : A ≤ |A| * w ^ N := by
  have h1 : 1 ≤ w ^ N := one_le_pow₀ hw
  nlinarith [le_abs_self A, abs_nonneg A]

theorem pEM_le {t X : ℝ} (ht : 0 < t) : ∃ C, ∀ w, 1 ≤ w → pEM t X w ≤ C * w ^ 15 := by
  refine ⟨|c₁' t X ^ 2 / (4 * t)| + |(cZ t X + 12) * (cξ t X + 1) / 2| + |2 * cξ t X| +
    |2 * (cZ t X + 12)| + |(2 : ℝ)| + |2 * cξ t X| + |Real.log ((√(4 * π * t))⁻¹)| + |π| +
    |3 * (X + 1) / 2| + |Real.log (1 / cg X) + t * π ^ 2 / 4|, ?_⟩
  intro w hw
  unfold pEM pM
  have h1 := monomial_le hw (c₁' t X ^ 2 / (4 * t)) (by norm_num : 14 ≤ 15)
  have h2 := monomial_le hw ((cZ t X + 12) * (cξ t X + 1) / 2) (by norm_num : 8 ≤ 15)
  have h3 := monomial_le hw (2 * cξ t X) (by norm_num : 7 ≤ 15)
  have h4 := monomial_le hw (2 * (cZ t X + 12)) (by norm_num : 1 ≤ 15)
  have h5 := const_le_pow hw (2 : ℝ) 15
  have h6 := const_le_pow hw (Real.log ((√(4 * π * t))⁻¹)) 15
  have h7 := monomial_le hw π (by norm_num : 12 ≤ 15)
  have h8 := monomial_le hw (3 * (X + 1) / 2) (by norm_num : 4 ≤ 15)
  have h9 := const_le_pow hw (Real.log (1 / cg X) + t * π ^ 2 / 4) 15
  rw [pow_one] at h4
  have := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add h1 h2) h3) h4) h5) h3) h6) h7) h8) h9
  refine this.trans (le_of_eq ?_)
  ring

theorem pET_le {t X : ℝ} (ht : 0 < t) : ∃ C, ∀ w, 1 ≤ w → pET t X w ≤ C * w ^ 15 := by
  refine ⟨|c₁' t X ^ 2 / (4 * t)| + |(1 : ℝ)| + |4 * √t + √(64 * π * t)| +
    |Real.log ((√(4 * π * t))⁻¹)| + |π| + |3 * (X + 1) / 2| +
    |Real.log (1 / cg X) + t * π ^ 2 / 4|, ?_⟩
  intro w hw
  unfold pET pT
  have h1 := monomial_le hw (c₁' t X ^ 2 / (4 * t)) (by norm_num : 14 ≤ 15)
  have h2 := monomial_le hw (1 : ℝ) (by norm_num : 12 ≤ 15)
  have h3 := const_le_pow hw (4 * √t + √(64 * π * t)) 15
  have h6 := const_le_pow hw (Real.log ((√(4 * π * t))⁻¹)) 15
  have h7 := monomial_le hw π (by norm_num : 12 ≤ 15)
  have h8 := monomial_le hw (3 * (X + 1) / 2) (by norm_num : 4 ≤ 15)
  have h9 := const_le_pow hw (Real.log (1 / cg X) + t * π ^ 2 / 4) 15
  rw [one_mul] at h2
  have := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h6)
    h7) h8) h9
  refine this.trans (le_of_eq ?_)
  ring

theorem tendsto_Emed {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    Tendsto (fun w => Emed t X w) atTop (𝓝 0) := by
  obtain ⟨C₁, hC₁⟩ := pEM_le (X := X) ht
  obtain ⟨C₂, hC₂⟩ := pET_le (X := X) ht
  have h1 := tendsto_exp_neg_pow_add (by positivity : (0 : ℝ) < 1 / (6400 * t))
    (by norm_num : 1 ≤ 16) (p := pEM t X) (C := C₁) (fun w hw => hC₁ w hw)
  have h2 := tendsto_exp_neg_pow_add (by positivity : (0 : ℝ) < 1 / (25600 * t))
    (by norm_num : 1 ≤ 16) (p := pET t X) (C := C₂) (fun w hw => hC₂ w hw)
  have h := h1.add h2
  rw [add_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop 1] with w hw
    have hw0 : 0 ≤ w := by linarith
    have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
    have hMm0 : 0 ≤ Mmed t X w := Mmed_nonneg (by unfold cZ cξ; positivity)
    have hTm0 := Tmed_nonneg (X := X) ht hw0
    have hΓ0 : 0 ≤ Γmaj t X (w ^ 4) := Γmaj_nonneg (by positivity)
    unfold Emed
    positivity
  · filter_upwards [eventually_ge_atTop 1] with w hw
    exact Emed_le_exp ht hX0 hw

theorem tendsto_Dmed {t : ℝ} (ht : 0 < t) : Tendsto (fun w => Dmed t w) atTop (𝓝 0) := by
  have h4 : Tendsto (fun w : ℝ => β₄maj t (w ^ 4)) atTop (𝓝 0) :=
    (tendsto_β₄maj ht).comp (tendsto_pow_atTop (by norm_num))
  have h := ((tendsto_β₃maj t).add h4).const_mul (Real.exp 1 / √(2 * π * t))
  simpa [Dmed] using h

end Soma.Holonics.RH.EventMedium
