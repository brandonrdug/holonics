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

end Soma.Holonics.RH.DescentApproximation
