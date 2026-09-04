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

end Soma.Holonics.RH.EventMedium
