import Mathlib
import ElementaryHolonics.RH.EventLarge

/-!
# RT4: the approximation theorem

`heatE t ξ (J_t s) = γ_t'(s) (F_t(s) + R_t(s))` with `F_t` the absolutely convergent series of
main terms and `R_t` the remainder, which vanishes uniformly on `|Re s| ≤ X` as `Im s → ∞`.
-/

noncomputable section

namespace Soma.Holonics.RH.DescentApproximation

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.DescentComb
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventHorizontal
open Soma.Holonics.RH.EventAssembly
open Soma.Holonics.RH.EventMainRange
open Soma.Holonics.RH.EventMedium
open Soma.Holonics.RH.EventLarge

/-! ## The series of main terms -/

/-- The `n`-th main term `e^{−t log²|n|} |n|^{−s}` (zero at `n = 0`). -/
def Fterm (t : ℝ) (s : ℂ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else
    Complex.exp (-(t : ℂ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ) ^ 2) *
      Complex.exp (-s * ((Real.log |(n : ℝ)| : ℝ) : ℂ))

/-- `F_t(s) = Σ_n Fterm t s n`. -/
def Ft (t : ℝ) (s : ℂ) : ℂ := ∑' n : ℤ, Fterm t s n

theorem Fterm_of_ne (t : ℝ) (s : ℂ) {n : ℤ} (hn : n ≠ 0) :
    Fterm t s n = Complex.exp (-(t : ℂ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ) ^ 2) *
      Complex.exp (-s * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) := by
  simp [Fterm, hn]

theorem norm_Fterm (t : ℝ) (s : ℂ) {n : ℤ} (hn : n ≠ 0) :
    ‖Fterm t s n‖ = Real.exp (-t * Real.log |(n : ℝ)| ^ 2) *
      Real.exp (-s.re * Real.log |(n : ℝ)|) := by
  rw [Fterm_of_ne t s hn, norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp [Complex.mul_re, sq]
  · simp [Complex.mul_re]

theorem log_abs_nonneg {n : ℤ} (hn : n ≠ 0) : 0 ≤ Real.log |(n : ℝ)| := by
  apply Real.log_nonneg
  have := Int.one_le_abs hn
  exact_mod_cast this

/-- The Gaussian in `log|n|` is dominated by `|n|^{−3/2}` with an explicit constant. -/
theorem exp_neg_mul_log_sq_le {a : ℝ} (ha : 0 < a) {n : ℤ} (hn : n ≠ 0) {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (b * Real.log |(n : ℝ)| - a * Real.log |(n : ℝ)| ^ 2) ≤
      Real.exp (b ^ 2 / (2 * a) + 9 / (8 * a)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  set L := Real.log |(n : ℝ)| with hL
  have hL0 : 0 ≤ L := log_abs_nonneg hn
  have hna : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  rw [Real.rpow_def_of_pos hna, ← hL, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e1 : b * L - a / 2 * L ^ 2 ≤ b ^ 2 / (2 * a) := by
    have : 0 ≤ a / 2 * (L - b / a) ^ 2 := by positivity
    have : a / 2 * (L - b / a) ^ 2 = a / 2 * L ^ 2 - b * L + b ^ 2 / (2 * a) := by
      field_simp
      ring
    linarith
  have e2 : -(a / 2) * L ^ 2 ≤ -(3 / 2) * L + 9 / (8 * a) := by
    have : 0 ≤ a / 2 * (L - 3 / (2 * a)) ^ 2 := by positivity
    have : a / 2 * (L - 3 / (2 * a)) ^ 2 = a / 2 * L ^ 2 - 3 / 2 * L + 9 / (8 * a) := by
      field_simp
      ring
    linarith
  nlinarith

theorem norm_Fterm_le {t : ℝ} (ht : 0 < t) {X : ℝ} {s : ℂ} (hX : |s.re| ≤ X) (n : ℤ) :
    ‖Fterm t s n‖ ≤ Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · subst hn
    simp [Fterm]
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) hX
  have hL0 := log_abs_nonneg hn
  rw [norm_Fterm t s hn, ← Real.exp_add]
  have hx : -s.re ≤ X := by linarith [neg_abs_le s.re]
  calc Real.exp (-t * Real.log |(n : ℝ)| ^ 2 + -s.re * Real.log |(n : ℝ)|)
      ≤ Real.exp (X * Real.log |(n : ℝ)| - t * Real.log |(n : ℝ)| ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hx hL0]
    _ ≤ Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
        exp_neg_mul_log_sq_le ht hn hX0

/-- `Σ_n |n|^{−3/2}` over the integers. -/
def Z32 : ℝ := ∑' n : ℤ, |(n : ℝ)| ^ (-(3 / 2 : ℝ))

theorem summable_Z32 : Summable (fun n : ℤ => |(n : ℝ)| ^ (-(3 / 2 : ℝ))) :=
  summable_abs_int_rpow (by norm_num)

theorem summable_norm_Fterm {t : ℝ} (ht : 0 < t) (s : ℂ) :
    Summable (fun n : ℤ => ‖Fterm t s n‖) := by
  refine (summable_Z32.mul_left (Real.exp (|s.re| ^ 2 / (2 * t) + 9 / (8 * t)))).of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => norm_Fterm_le ht le_rfl n)

theorem summable_Fterm {t : ℝ} (ht : 0 < t) (s : ℂ) : Summable (Fterm t s) :=
  (summable_norm_Fterm ht s).of_norm

theorem tsum_norm_Fterm_le {t : ℝ} (ht : 0 < t) {X : ℝ} {s : ℂ} (hX : |s.re| ≤ X) :
    ∑' n : ℤ, ‖Fterm t s n‖ ≤ Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * Z32 := by
  unfold Z32
  rw [← tsum_mul_left]
  exact hasSum_le (fun n => norm_Fterm_le ht hX n) (summable_norm_Fterm ht s).hasSum
    (summable_Z32.mul_left _).hasSum

/-! ## The remainder -/

/-- `R_t(s) = heatE t ξ (J_t s) / γ_t'(s) − F_t(s)`. -/
def Rt (t : ℝ) (s : ℂ) : ℂ := heatE t riemannXi (J t s) / γt' t s - Ft t s

theorem heatE_J_eq {t : ℝ} {s : ℂ} (hγ : γt' t s ≠ 0) :
    heatE t riemannXi (J t s) = γt' t s * (Ft t s + Rt t s) := by
  unfold Rt
  field_simp
  first | done | ring

/-- The `n`-th difference between the flowed event and its main term. -/
def dterm (t : ℝ) (s : ℂ) (n : ℤ) : ℂ :=
  (∫ u : ℝ, flowedTerm t (J t s) n u) - γt' t s * Fterm t s n

theorem hasSum_dterm {t : ℝ} (ht : 0 < t) (s : ℂ) :
    HasSum (dterm t s) (heatE t riemannXi (J t s) - γt' t s * Ft t s) := by
  unfold dterm Ft
  exact (hasSum_flowedTerm_of_pos ht (J t s)).sub ((summable_Fterm ht s).hasSum.mul_left _)

theorem Rt_eq_tsum {t : ℝ} (ht : 0 < t) {s : ℂ} (hγ : γt' t s ≠ 0) :
    Rt t s = (∑' n : ℤ, dterm t s n) / γt' t s := by
  rw [(hasSum_dterm ht s).tsum_eq]
  unfold Rt
  field_simp
  first | done | ring

theorem summable_norm_dterm {t : ℝ} (ht : 0 < t) (s : ℂ) :
    Summable (fun n : ℤ => ‖dterm t s n‖) := by
  refine ((summable_norm_integral_flowedTerm ht (J t s)).add
    ((summable_norm_Fterm ht s).mul_left ‖γt' t s‖)).of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_)
  unfold dterm
  calc ‖(∫ u : ℝ, flowedTerm t (J t s) n u) - γt' t s * Fterm t s n‖
      ≤ ‖∫ u : ℝ, flowedTerm t (J t s) n u‖ + ‖γt' t s * Fterm t s n‖ := norm_sub_le _ _
    _ = ‖∫ u : ℝ, flowedTerm t (J t s) n u‖ + ‖γt' t s‖ * ‖Fterm t s n‖ := by rw [norm_mul]

theorem norm_Rt_le_tsum {t : ℝ} (ht : 0 < t) {s : ℂ} (hγ : γt' t s ≠ 0) :
    ‖Rt t s‖ ≤ (∑' n : ℤ, ‖dterm t s n‖) / ‖γt' t s‖ := by
  rw [Rt_eq_tsum ht hγ, norm_div]
  gcongr
  exact norm_tsum_le_tsum_norm (summable_norm_dterm ht s)

theorem dterm_zero (t : ℝ) (s : ℂ) : dterm t s 0 = 0 := by
  unfold dterm
  have h1 : flowedTerm t (J t s) 0 = fun _ => 0 := by
    funext u
    unfold flowedTerm
    rw [lapTerm_zero, mul_zero]
  simp [h1, Fterm]

/-! ## The pointwise bound on the three ranges -/

theorem Bmaj_nonneg {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {u : ℝ} (hu : 0 < u) :
    0 ≤ Bmaj t X u := by
  have hA : 0 ≤ Amaj t u := by unfold Amaj; positivity
  have hB : 0 ≤ Bmaj' t u := by unfold Bmaj'; positivity
  have hD := Dmaj_nonneg ht hu.le
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hE : 0 ≤ Emaj t X u := by
    have hM : 0 ≤ Mmaj t X u := Mmaj_nonneg (by unfold cZ cξ; positivity)
    have hT := Tmaj_nonneg (X := X) ht hu.le
    have hΓ : 0 ≤ Γmaj t X u := Γmaj_nonneg hu.le
    unfold Emaj
    positivity
  unfold Bmaj
  positivity

theorem γt'_ne_zero_of {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    (hs2 : 2 ≤ ‖s‖) : γt' t s ≠ 0 := by
  have hs0 : 0 < ‖s‖ := by linarith
  have hlow := norm_γt'_ge ht.le hX0 hX hs2
  have hpos : 0 < cg X * ‖s‖ ^ 2 * ‖s‖ ^ (-((X + 1) / 2)) * Real.exp (-(π * ‖s‖ / 2)) *
      Real.exp (-(t * π ^ 2 / 4)) :=
    mul_pos (mul_pos (mul_pos (mul_pos (cg_pos X) (by positivity)) (Real.rpow_pos_of_pos hs0 _))
      (Real.exp_pos _)) (Real.exp_pos _)
  exact norm_pos_iff.mp (hpos.trans_le hlow)

/-- The tail bound term `e^{X L − (3c/8) L²}`, zero at `n = 0`. -/
def tterm (t X : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (X * Real.log |(n : ℝ)| - 3 * cmin t / 8 * Real.log |(n : ℝ)| ^ 2)

theorem tterm_nonneg (t X : ℝ) (n : ℤ) : 0 ≤ tterm t X n := by
  unfold tterm
  split_ifs <;> positivity

theorem tterm_le {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) (n : ℤ) :
    tterm t X n ≤ Real.exp (X ^ 2 / (2 * (3 * cmin t / 8)) + 9 / (8 * (3 * cmin t / 8))) *
      |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hc := cmin_pos ht
  unfold tterm
  split_ifs with hn
  · subst hn; simp
  · exact exp_neg_mul_log_sq_le (by positivity) hn hX0

theorem summable_tterm {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) : Summable (tterm t X) :=
  (summable_Z32.mul_left _).of_nonneg_of_le (tterm_nonneg t X) (tterm_le ht hX0)

theorem tsum_tterm_le {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    ∑' n : ℤ, tterm t X n ≤
      Real.exp (X ^ 2 / (2 * (3 * cmin t / 8)) + 9 / (8 * (3 * cmin t / 8))) * Z32 := by
  unfold Z32
  rw [← tsum_mul_left]
  exact hasSum_le (tterm_le ht hX0) (summable_tterm ht hX0).hasSum (summable_Z32.mul_left _).hasSum

/-- **The pointwise bound.** Eventually in `w`, at `s = x + i w¹²` with `|x| ≤ X`, every
difference `dterm t s n` is at most
`‖γ_t'(s)‖ (‖Fterm n‖ Bmaj t X w⁴ + 13 e^{−(c/8) w⁸} tterm n)`. -/
theorem norm_dterm_le {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    ∀ᶠ w in atTop, ∀ s : ℂ, |s.re| ≤ X → s.im = w ^ 12 → ∀ n : ℤ,
      ‖dterm t s n‖ ≤ ‖γt' t s‖ * (‖Fterm t s n‖ * Bmaj t X (w ^ 4) +
        13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n) := by
  have hc := cmin_pos ht
  filter_upwards [event_medium ht hX0, event_large ht hX0, eventually_ge_atTop 1,
    eventually_ge_atTop (u₀ t X)] with w hmed hlarge hw1 hwu
  intro s hX hy n
  have hw0 : 0 < w := by linarith
  have hw4 : 1 ≤ w ^ 4 := one_le_pow₀ hw1
  have h1_4 : w ≤ w ^ 4 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
  have hBm := Bmaj_nonneg ht hX0 (by positivity : (0 : ℝ) < w ^ 4)
  have hE0 : 0 ≤ Real.exp (-(cmin t / 8) * w ^ 8) := (Real.exp_pos _).le
  have htt := tterm_nonneg t X n
  by_cases hn : n = 0
  · subst hn
    rw [dterm_zero]
    simp [Fterm, tterm]
  set L : ℝ := Real.log |(n : ℝ)| with hLdef
  have hL0 : 0 ≤ L := log_abs_nonneg hn
  have hy' : s.im = (w ^ 4) ^ 3 := by rw [hy]; ring
  have hcmt : cmin t ≤ t := by
    unfold cmin
    have := min_le_left t 1
    linarith
  by_cases hmain : L ≤ w ^ 4
  · obtain ⟨heq, hr⟩ := event_main ht hX0 (h1_4.trans' hwu) hX hy' hn hmain
    have hd : dterm t s n = γt' t s * Fterm t s n * rdef t s L ((w ^ 4) ^ 2 / 20) := by
      unfold dterm
      rw [heq, Fterm_of_ne t s hn]
      ring
    rw [hd, norm_mul, norm_mul]
    have : ‖γt' t s‖ * ‖Fterm t s n‖ * ‖rdef t s L ((w ^ 4) ^ 2 / 20)‖ ≤
        ‖γt' t s‖ * ‖Fterm t s n‖ * Bmaj t X (w ^ 4) := by gcongr
    have h2 : 0 ≤ ‖γt' t s‖ * (13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n) := by
      positivity
    nlinarith
  · push_neg at hmain
    -- the tail: both the event and the main term are small
    have hx : -s.re ≤ X := by linarith [neg_abs_le s.re]
    have hev : ‖∫ v : ℝ, flowedTerm t (J t s) n v‖ ≤
        12 * ‖γt' t s‖ * Real.exp (-s.re * L) * Real.exp (-(cmin t / 2) * L ^ 2) := by
      by_cases hmed' : L ≤ w ^ 7
      · have := hmed s hX hy n hn hmed'
        refine this.trans ?_
        have hee : Real.exp (-(t / 2) * L ^ 2) ≤ Real.exp (-(cmin t / 2) * L ^ 2) :=
          Real.exp_le_exp.mpr (by nlinarith [sq_nonneg L])
        gcongr
      · push_neg at hmed'
        have := hlarge s hX hy n hn hmed'.le
        refine this.trans ?_
        have := norm_nonneg (γt' t s)
        have := Real.exp_pos (-s.re * L)
        have := Real.exp_pos (-(cmin t / 2) * L ^ 2)
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (γt' t s)) (Real.exp_pos (-s.re * L)).le)
          (Real.exp_pos (-(cmin t / 2) * L ^ 2)).le]
    have hF : ‖Fterm t s n‖ ≤ Real.exp (-s.re * L) * Real.exp (-(cmin t / 2) * L ^ 2) := by
      rw [norm_Fterm t s hn, mul_comm]
      have hee : Real.exp (-t * L ^ 2) ≤ Real.exp (-(cmin t / 2) * L ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg L])
      gcongr
    have htail : Real.exp (-s.re * L) * Real.exp (-(cmin t / 2) * L ^ 2) ≤
        Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n := by
      unfold tterm
      rw [if_neg hn, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hL2 : w ^ 8 ≤ L ^ 2 := by
        calc w ^ 8 = (w ^ 4) ^ 2 := by ring
          _ ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hmain.le 2
      nlinarith [mul_le_mul_of_nonneg_right hx hL0]
    have hd : ‖dterm t s n‖ ≤ ‖∫ v : ℝ, flowedTerm t (J t s) n v‖ + ‖γt' t s‖ * ‖Fterm t s n‖ := by
      unfold dterm
      rw [← norm_mul]
      exact norm_sub_le _ _
    have hγ0 := norm_nonneg (γt' t s)
    have hF0 := norm_nonneg (Fterm t s n)
    calc ‖dterm t s n‖ ≤ ‖∫ v : ℝ, flowedTerm t (J t s) n v‖ + ‖γt' t s‖ * ‖Fterm t s n‖ := hd
      _ ≤ 12 * ‖γt' t s‖ * Real.exp (-s.re * L) * Real.exp (-(cmin t / 2) * L ^ 2) +
          ‖γt' t s‖ * (Real.exp (-s.re * L) * Real.exp (-(cmin t / 2) * L ^ 2)) := by
          gcongr
      _ = ‖γt' t s‖ * (13 * (Real.exp (-s.re * L) * Real.exp (-(cmin t / 2) * L ^ 2))) := by ring
      _ ≤ ‖γt' t s‖ * (13 * (Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n)) := by gcongr
      _ ≤ ‖γt' t s‖ * (‖Fterm t s n‖ * Bmaj t X (w ^ 4) +
          13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n) := by
          apply mul_le_mul_of_nonneg_left _ hγ0
          nlinarith [mul_nonneg hF0 hBm]

/-! ## The approximation theorem -/

/-- The uniform remainder bound `ρ(w)`. -/
def ρ (t X w : ℝ) : ℝ :=
  Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * Z32 * Bmaj t X (w ^ 4) +
    13 * Real.exp (-(cmin t / 8) * w ^ 8) *
      (Real.exp (X ^ 2 / (2 * (3 * cmin t / 8)) + 9 / (8 * (3 * cmin t / 8))) * Z32)

theorem tendsto_ρ {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) : Tendsto (ρ t X) atTop (𝓝 0) := by
  have hc := cmin_pos ht
  have h1 : Tendsto (fun w : ℝ => Bmaj t X (w ^ 4)) atTop (𝓝 0) :=
    (tendsto_Bmaj ht hX0).comp (tendsto_pow_atTop (by norm_num))
  have h2 : Tendsto (fun w : ℝ => Real.exp (-(cmin t / 8) * w ^ 8)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by linarith) (tendsto_pow_atTop (by norm_num)))
  have h := (h1.const_mul (Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * Z32)).add
    ((h2.const_mul 13).mul_const
      (Real.exp (X ^ 2 / (2 * (3 * cmin t / 8)) + 9 / (8 * (3 * cmin t / 8))) * Z32))
  have h0 : Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * Z32 * 0 + 13 * 0 *
      (Real.exp (X ^ 2 / (2 * (3 * cmin t / 8)) + 9 / (8 * (3 * cmin t / 8))) * Z32) = 0 := by ring
  rw [h0] at h
  show Tendsto (fun w => ρ t X w) atTop (𝓝 0)
  unfold ρ
  exact h

/-- **The approximation theorem (RT4).** Eventually in `w`, for every `s = x + i w¹²` with
`|x| ≤ X`: `γ_t'(s) ≠ 0`, `heatE t ξ (J_t s) = γ_t'(s)(F_t(s) + R_t(s))`, and
`‖R_t(s)‖ ≤ ρ(w)` with `ρ → 0`. -/
theorem descent_approximation {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    ∀ᶠ w in atTop, ∀ s : ℂ, |s.re| ≤ X → s.im = w ^ 12 →
      γt' t s ≠ 0 ∧ heatE t riemannXi (J t s) = γt' t s * (Ft t s + Rt t s) ∧
        ‖Rt t s‖ ≤ ρ t X w := by
  have hc := cmin_pos ht
  filter_upwards [norm_dterm_le ht hX0, eventually_ge_atTop 2] with w hpt hw2
  intro s hX hy
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have h1_12 : w ≤ w ^ 12 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 12 := pow_le_pow_right₀ hw1 (by norm_num)
  have hy' : s.im = (w ^ 4) ^ 3 := by rw [hy]; ring
  have hsu : w ^ 12 ≤ ‖s‖ := by
    have := norm_s_ge hy' (by positivity)
    rw [show (w ^ 4) ^ 3 = w ^ 12 by ring] at this
    exact this
  have hs2 : 2 ≤ ‖s‖ := by linarith
  have hγ := γt'_ne_zero_of ht hX0 hX hs2
  have hγpos : 0 < ‖γt' t s‖ := norm_pos_iff.mpr hγ
  refine ⟨hγ, heatE_J_eq hγ, ?_⟩
  have hBm := Bmaj_nonneg ht hX0 (by positivity : (0 : ℝ) < w ^ 4)
  have hE0 : 0 ≤ Real.exp (-(cmin t / 8) * w ^ 8) := (Real.exp_pos _).le
  -- the summable majorant
  have hsF := summable_norm_Fterm ht s
  have hst := summable_tterm ht hX0
  have hmaj : Summable (fun n : ℤ => ‖Fterm t s n‖ * Bmaj t X (w ^ 4) +
      13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n) :=
    (hsF.mul_right _).add (hst.mul_left _)
  have hsum : ∑' n : ℤ, ‖dterm t s n‖ ≤ ‖γt' t s‖ * ∑' n : ℤ, (‖Fterm t s n‖ * Bmaj t X (w ^ 4) +
      13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n) := by
    rw [← tsum_mul_left]
    exact hasSum_le (fun n => hpt s hX hy n) (summable_norm_dterm ht s).hasSum
      (hmaj.mul_left _).hasSum
  have hsplit : ∑' n : ℤ, (‖Fterm t s n‖ * Bmaj t X (w ^ 4) +
      13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n) =
      (∑' n : ℤ, ‖Fterm t s n‖) * Bmaj t X (w ^ 4) +
        13 * Real.exp (-(cmin t / 8) * w ^ 8) * ∑' n : ℤ, tterm t X n := by
    rw [(hsF.mul_right _).tsum_add (hst.mul_left _), tsum_mul_right, tsum_mul_left]
  have hF := tsum_norm_Fterm_le ht hX
  have hT := tsum_tterm_le ht hX0
  calc ‖Rt t s‖ ≤ (∑' n : ℤ, ‖dterm t s n‖) / ‖γt' t s‖ := norm_Rt_le_tsum ht hγ
    _ ≤ (‖γt' t s‖ * ∑' n : ℤ, (‖Fterm t s n‖ * Bmaj t X (w ^ 4) +
          13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n)) / ‖γt' t s‖ := by gcongr
    _ = ∑' n : ℤ, (‖Fterm t s n‖ * Bmaj t X (w ^ 4) +
          13 * Real.exp (-(cmin t / 8) * w ^ 8) * tterm t X n) := by
        rw [mul_div_cancel_left₀ _ hγpos.ne']
    _ = (∑' n : ℤ, ‖Fterm t s n‖) * Bmaj t X (w ^ 4) +
        13 * Real.exp (-(cmin t / 8) * w ^ 8) * ∑' n : ℤ, tterm t X n := hsplit
    _ ≤ (Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * Z32) * Bmaj t X (w ^ 4) +
        13 * Real.exp (-(cmin t / 8) * w ^ 8) *
          (Real.exp (X ^ 2 / (2 * (3 * cmin t / 8)) + 9 / (8 * (3 * cmin t / 8))) * Z32) := by
        gcongr
    _ = ρ t X w := rfl

end Soma.Holonics.RH.DescentApproximation
