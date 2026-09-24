import Mathlib
import ElementaryHolonics.RH.EventMedium

/-!
# RT3 (iii-l): the large range

For `L = log |n| ≥ w⁷` the absolute Gaussian bound of RT1 already beats `γ_t(s)`: the event is at
most `‖γ_t(s)‖ e^{−Re s · L} e^{−(c/2) L²}` with `c = min t 1 / 8`, eventually in `w`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventLarge

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.DescentComb
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventHorizontal
open Soma.Holonics.RH.EventMainRange
open Soma.Holonics.RH.EventMedium

/-- The Gaussian rate of RT1's absolute bound. -/
def cmin (t : ℝ) : ℝ := min t 1 / 8

theorem cmin_pos {t : ℝ} (ht : 0 < t) : 0 < cmin t := by
  unfold cmin
  have : 0 < min t 1 := lt_min ht one_pos
  positivity

/-- `cJ = X + 2 + 18t` majorizes `(|Re J_t(s) − ½| + 1) / w`. -/
def cJ (t X : ℝ) : ℝ := X + 2 + 18 * t

theorem re_J_bound {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X) {w : ℝ}
    (hw : 1 ≤ w) (hs2 : 2 ≤ ‖s‖) (hs2u : ‖s‖ ≤ 2 * w ^ 12) :
    |(J t s).re - 1 / 2| + 1 ≤ cJ t X * w := by
  have hs1 : 1 ≤ ‖s‖ := by linarith
  have hlog := log_norm_s_le_med hw hs1 hs2u
  have hΛ := norm_Λ_le hs2
  have hre : |(Λs s).re| ≤ ‖Λs s‖ := Complex.abs_re_le_norm _
  have hJ : (J t s).re = s.re + t * (Λs s).re := by
    unfold J
    simp [Complex.add_re, Complex.mul_re]
  rw [hJ]
  unfold cJ
  have h1 : |s.re + t * (Λs s).re - 1 / 2| ≤ |s.re| + t * |(Λs s).re| + 1 / 2 := by
    calc |s.re + t * (Λs s).re - 1 / 2| ≤ |s.re + t * (Λs s).re| + |(1 / 2 : ℝ)| := abs_sub _ _
      _ ≤ |s.re| + |t * (Λs s).re| + 1 / 2 := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          linarith [abs_add_le s.re (t * (Λs s).re)]
      _ = |s.re| + t * |(Λs s).re| + 1 / 2 := by rw [abs_mul, abs_of_pos ht]
  have h2 : t * |(Λs s).re| ≤ t * (12 * w + 6) := by
    apply mul_le_mul_of_nonneg_left _ ht.le
    linarith
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hw), mul_nonneg hX0 (sub_nonneg.mpr hw)]

theorem K₂_le {t : ℝ} (ht : 0 < t) (z : ℂ) :
    K₂ t z ≤ 2 * Mφ * √(4 * π / t) * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / t) := by
  unfold K₂
  have hM := Mφ_pos
  have ha := abs_nonneg (z.re - 1 / 2)
  have e1 : √(π / (t / 4)) = √(4 * π / t) := by
    congr 1
    field_simp
  have e2 : √(π / (t / 2)) ≤ √(4 * π / t) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  have e3 : Real.exp (|z.re - 1 / 2| ^ 2 / t) ≤ Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / t) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith
  have e4 : Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) ≤
      Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / t) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) ht]
    nlinarith [sq_nonneg (|z.re - 1 / 2| + 1)]
  rw [e1]
  have h1 : Mφ * Real.exp (|z.re - 1 / 2| ^ 2 / t) * √(4 * π / t) ≤
      Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / t) * √(4 * π / t) := by gcongr
  have h2 : Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) * √(π / (t / 2)) ≤
      Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / t) * √(4 * π / t) := by gcongr
  linarith

/-- The majorant of `K₂ e^{−c w¹⁴/4}` in `w`. -/
def Kmaj (t X w : ℝ) : ℝ :=
  2 * Mφ * √(4 * π / t) * Real.exp ((cJ t X * w) ^ 2 / t) * Real.exp (-(cmin t / 4) * w ^ 14)

theorem K₂_mul_le_Kmaj {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X) {w : ℝ}
    (hw : 1 ≤ w) (hs2 : 2 ≤ ‖s‖) (hs2u : ‖s‖ ≤ 2 * w ^ 12) {L : ℝ} (hL : w ^ 7 ≤ L) :
    K₂ t (J t s) * Real.exp (-(cmin t / 4) * L ^ 2) ≤ Kmaj t X w := by
  have hc := cmin_pos ht
  have hJ := re_J_bound ht hX0 hX hw hs2 hs2u
  have hK := K₂_le ht (J t s)
  have hw0 : 0 ≤ w := by linarith
  have e1 : Real.exp ((|(J t s).re - 1 / 2| + 1) ^ 2 / t) ≤ Real.exp ((cJ t X * w) ^ 2 / t) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ ht.le
    exact pow_le_pow_left₀ (by positivity) hJ 2
  have e2 : Real.exp (-(cmin t / 4) * L ^ 2) ≤ Real.exp (-(cmin t / 4) * w ^ 14) := by
    apply Real.exp_le_exp.mpr
    have : w ^ 14 ≤ L ^ 2 := by
      calc w ^ 14 = (w ^ 7) ^ 2 := by ring
        _ ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hL 2
    nlinarith
  unfold Kmaj
  have hM := Mφ_pos
  calc K₂ t (J t s) * Real.exp (-(cmin t / 4) * L ^ 2)
      ≤ (2 * Mφ * √(4 * π / t) * Real.exp ((|(J t s).re - 1 / 2| + 1) ^ 2 / t)) *
        Real.exp (-(cmin t / 4) * w ^ 14) := by
        apply mul_le_mul hK e2 (Real.exp_pos _).le (by positivity)
    _ ≤ 2 * Mφ * √(4 * π / t) * Real.exp ((cJ t X * w) ^ 2 / t) *
        Real.exp (-(cmin t / 4) * w ^ 14) := by gcongr

/-- The exponent majorizing `Kmaj · Γmaj`. -/
def pK (t X w : ℝ) : ℝ :=
  Real.log (2 * Mφ * √(4 * π / t)) + cJ t X ^ 2 / t * w ^ 2 + π * w ^ 12 +
    3 * (X + 1) / 2 * w ^ 4 + (Real.log (1 / cg X) + t * π ^ 2 / 4)

theorem Kmaj_mul_Γmaj_le {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {w : ℝ} (hw : 1 ≤ w) :
    Kmaj t X w * Γmaj t X (w ^ 4) ≤ Real.exp (-(cmin t / 4) * w ^ 14 + pK t X w) := by
  have hw4 : 1 ≤ w ^ 4 := one_le_pow₀ hw
  have hΓ := Γmaj_le_exp (t := t) ht hX0 hw4
  have hM := Mφ_pos
  have hk : 2 * Mφ * √(4 * π / t) = Real.exp (Real.log (2 * Mφ * √(4 * π / t))) :=
    (Real.exp_log (by positivity)).symm
  unfold Kmaj
  calc 2 * Mφ * √(4 * π / t) * Real.exp ((cJ t X * w) ^ 2 / t) *
        Real.exp (-(cmin t / 4) * w ^ 14) * Γmaj t X (w ^ 4)
      ≤ Real.exp (Real.log (2 * Mφ * √(4 * π / t))) * Real.exp ((cJ t X * w) ^ 2 / t) *
        Real.exp (-(cmin t / 4) * w ^ 14) *
        Real.exp (π * (w ^ 4) ^ 3 + 3 * (X + 1) / 2 * w ^ 4 +
          (Real.log (1 / cg X) + t * π ^ 2 / 4)) := by
        rw [← hk]
        gcongr
    _ = Real.exp (-(cmin t / 4) * w ^ 14 + pK t X w) := by
        simp only [← Real.exp_add]
        congr 1
        unfold pK
        field_simp
        ring

theorem pK_le {t X : ℝ} (ht : 0 < t) : ∃ C, ∀ w, 1 ≤ w → pK t X w ≤ C * w ^ 13 := by
  refine ⟨|Real.log (2 * Mφ * √(4 * π / t))| + |cJ t X ^ 2 / t| + |π| + |3 * (X + 1) / 2| +
    |Real.log (1 / cg X) + t * π ^ 2 / 4|, ?_⟩
  intro w hw
  unfold pK
  have h1 := const_le_pow hw (Real.log (2 * Mφ * √(4 * π / t))) 13
  have h2 := monomial_le hw (cJ t X ^ 2 / t) (by norm_num : 2 ≤ 13)
  have h3 := monomial_le hw π (by norm_num : 12 ≤ 13)
  have h4 := monomial_le hw (3 * (X + 1) / 2) (by norm_num : 4 ≤ 13)
  have h5 := const_le_pow hw (Real.log (1 / cg X) + t * π ^ 2 / 4) 13
  have := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
  refine this.trans (le_of_eq ?_)
  ring

theorem tendsto_Kmaj_mul_Γmaj {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    Tendsto (fun w => Kmaj t X w * Γmaj t X (w ^ 4)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := pK_le (X := X) ht
  have h := tendsto_exp_neg_pow_add (by have := cmin_pos ht; positivity : (0 : ℝ) < cmin t / 4)
    (by norm_num : 1 ≤ 14) (p := pK t X) (C := C) (fun w hw => hC w hw)
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop 1] with w hw
    have hM := Mφ_pos
    have hΓ0 : 0 ≤ Γmaj t X (w ^ 4) := Γmaj_nonneg (by positivity)
    unfold Kmaj
    positivity
  · filter_upwards [eventually_ge_atTop 1] with w hw
    exact Kmaj_mul_Γmaj_le ht hX0 hw

/-- **The large-range event theorem.** Eventually in `w`, for `s = x + i w¹²` with `|x| ≤ X` and
every `n ≠ 0` with `log |n| ≥ w⁷`,
`‖event‖ ≤ ‖γ_t(s)‖ e^{−x log|n|} e^{−(c/2) log²|n|}` with `c = min t 1 / 8`. -/
theorem event_large {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    ∀ᶠ w in atTop, ∀ s : ℂ, |s.re| ≤ X → s.im = w ^ 12 → ∀ n : ℤ, n ≠ 0 →
      w ^ 7 ≤ Real.log |(n : ℝ)| →
      ‖∫ v : ℝ, flowedTerm t (J t s) n v‖ ≤
        ‖γt' t s‖ * Real.exp (-s.re * Real.log |(n : ℝ)|) *
          Real.exp (-(cmin t / 2) * Real.log |(n : ℝ)| ^ 2) := by
  have hc := cmin_pos ht
  have hK := (tendsto_order.1 (tendsto_Kmaj_mul_Γmaj ht hX0)).2 1 one_pos
  filter_upwards [eventually_ge_atTop (2 + 4 * X / cmin t), hK] with w hw hK1
  intro s hX hy n hn hL
  set L : ℝ := Real.log |(n : ℝ)| with hLdef
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    have := Int.one_le_abs hn
    exact_mod_cast this
  have hXc : 0 ≤ 4 * X / cmin t := by positivity
  have hw2 : 2 ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hw4 : 1 ≤ w ^ 4 := one_le_pow₀ hw1
  have h1_7 : w ≤ w ^ 7 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 7 := pow_le_pow_right₀ hw1 (by norm_num)
  have h1_12 : w ≤ w ^ 12 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 12 := pow_le_pow_right₀ hw1 (by norm_num)
  have hy' : s.im = (w ^ 4) ^ 3 := by rw [hy]; ring
  have hXw : X ≤ w ^ 12 := by
    have : X ≤ 4 * X / cmin t := by
      rw [le_div_iff₀ hc]
      have : cmin t ≤ 1 := by
        unfold cmin
        have := min_le_right t 1
        linarith
      nlinarith
    linarith
  have hXw' : X ≤ (w ^ 4) ^ 3 := by rw [show (w ^ 4) ^ 3 = w ^ 12 by ring]; exact hXw
  have hsu : w ^ 12 ≤ ‖s‖ := by
    have := norm_s_ge hy' (by positivity)
    rw [show (w ^ 4) ^ 3 = w ^ 12 by ring] at this
    exact this
  have hs2u : ‖s‖ ≤ 2 * w ^ 12 := by
    have := norm_s_le hX hy' hXw' (by positivity)
    rw [show (w ^ 4) ^ 3 = w ^ 12 by ring] at this
    exact this
  have hs2 : 2 ≤ ‖s‖ := by linarith
  have hs1 : 1 ≤ ‖s‖ := by linarith
  have hs0 : 0 < ‖s‖ := by linarith
  -- the absolute bound
  have habs : ‖∫ v : ℝ, flowedTerm t (J t s) n v‖ ≤ K₂ t (J t s) * Real.exp (-(cmin t) * L ^ 2) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have := integral_norm_flowedTerm_le_gaussian ht (J t s) hn
    unfold cmin
    exact this
  -- the three exponential factors
  have hsplit : Real.exp (-(cmin t) * L ^ 2) =
      Real.exp (-(cmin t / 4) * L ^ 2) * Real.exp (-(cmin t / 4) * L ^ 2) *
        Real.exp (-(cmin t / 2) * L ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hKm := K₂_mul_le_Kmaj ht hX0 hX hw1 hs2 hs2u hL
  have hs2u' : ‖s‖ ≤ 2 * (w ^ 4) ^ 3 := by rw [show (w ^ 4) ^ 3 = w ^ 12 by ring]; exact hs2u
  have hΓ := inv_γlow_le_Γmaj (t := t) ht hX0 hw4 hs1 hs2u'
  have hγpos := γlow_pos (t := t) (X := X) hs0
  have hΓpos : 0 < Γmaj t X (w ^ 4) := by
    have := Γmaj_nonneg (t := t) (X := X) (u := w ^ 4) (by positivity)
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hΓ
      have : 0 < 1 / γlow t X s := by positivity
      linarith
  have hKγ : Kmaj t X w ≤ γlow t X s := by
    have h1 : Kmaj t X w ≤ 1 / Γmaj t X (w ^ 4) := by
      rw [le_div_iff₀ hΓpos]
      linarith
    have h2 : 1 / Γmaj t X (w ^ 4) ≤ γlow t X s := by
      rw [div_le_iff₀ hΓpos]
      calc (1 : ℝ) = γlow t X s * (1 / γlow t X s) := by field_simp
        _ ≤ γlow t X s * Γmaj t X (w ^ 4) := by gcongr
    exact h1.trans h2
  have hγ := norm_γt'_ge ht.le hX0 hX hs2
  have hγlow : γlow t X s ≤ ‖γt' t s‖ := by
    unfold γlow
    exact hγ
  have hexpx : Real.exp (-(cmin t / 4) * L ^ 2) ≤ Real.exp (-s.re * L) := by
    apply Real.exp_le_exp.mpr
    have hx : s.re ≤ X := le_trans (le_abs_self _) hX
    have hcL : 4 * X ≤ cmin t * L := by
      have : 4 * X / cmin t ≤ L := by linarith
      rw [div_le_iff₀ hc] at this
      linarith
    nlinarith
  calc ‖∫ v : ℝ, flowedTerm t (J t s) n v‖
      ≤ K₂ t (J t s) * Real.exp (-(cmin t) * L ^ 2) := habs
    _ = (K₂ t (J t s) * Real.exp (-(cmin t / 4) * L ^ 2)) * Real.exp (-(cmin t / 4) * L ^ 2) *
        Real.exp (-(cmin t / 2) * L ^ 2) := by rw [hsplit]; ring
    _ ≤ ‖γt' t s‖ * Real.exp (-s.re * L) * Real.exp (-(cmin t / 2) * L ^ 2) := by
        gcongr
        exact hKm.trans (hKγ.trans hγlow)

end Soma.Holonics.RH.EventLarge
