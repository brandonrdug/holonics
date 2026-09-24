import Mathlib
import ElementaryHolonics.RH.EventGaussian

/-!
# RT3 (iii-f): the window against the full Gaussian

With `c = 3/(32t)`, `‖q‖ ≤ 1`, and `Re A ≥ 1/(8t)`: `‖gauss(v)‖ ≤ e^{8t} e^{−c v²}`. Hence the
tail beyond the window, `‖G − ∫_{−Y}^{Y} gauss‖ ≤ 2 e^{8t} √(2π/c) e^{−cY²/2}`, and the defect
integral `‖∫_{−Y}^{Y} gauss · D‖ ≤ 2 e^{8t} ((1608 h³/‖s‖² + 2π/(3‖s‖)) I₀ + 1608 I₃/‖s‖²)` with
`I₀ = √(π/c)`, `I₃ = 7 c^{−3/2} √(π/(3c/4))`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventWindow

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventGaussian

theorem abs_le_sq_div {t : ℝ} (ht : 0 < t) (v : ℝ) : |v| ≤ v ^ 2 / (32 * t) + 8 * t := by
  have h := sq_nonneg (|v| - 16 * t)
  have hv := sq_abs v
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  nlinarith

/-- The Gaussian majorant of `‖gauss‖`: `‖gauss(v)‖ ≤ e^{8t} e^{−(3/(32t)) v²}` when `‖q‖ ≤ 1`. -/
theorem norm_gauss_le' {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) {h : ℝ}
    (hq : ‖q s h‖ ≤ 1) (v : ℝ) :
    ‖gauss t s h v‖ ≤ Real.exp (8 * t) * Real.exp (-(3 / (32 * t)) * v ^ 2) := by
  have hA := re_A_ge ht hs hst
  refine (norm_gauss_le t s h v).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ‖q s h‖ * |v| ≤ |v| := by
    calc ‖q s h‖ * |v| ≤ 1 * |v| := by gcongr
      _ = |v| := one_mul _
  have h2 := abs_le_sq_div ht v
  have h3 : (A t s).re * v ^ 2 ≥ 1 / (8 * t) * v ^ 2 := by
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg v)
  have e : 8 * t + -(3 / (32 * t)) * v ^ 2 = -(1 / (8 * t)) * v ^ 2 + (v ^ 2 / (32 * t) + 8 * t) := by
    field_simp
    ring
  rw [e]
  linarith

theorem integrable_majorant {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : ℝ => |v| ^ 3 * Real.exp (-c * v ^ 2)) := by
  have hg := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 3 * c / 4)).const_mul
    (7 * c ^ (-(3 / 2 : ℝ)))
  refine hg.mono' ?_ (Eventually.of_forall fun v => ?_)
  · exact ((continuous_abs.pow 3).mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact cube_mul_exp_le' hc v

/-- **The tail beyond the window.** -/
theorem norm_G_sub_window_le {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖)
    {h : ℝ} (hq : ‖q s h‖ ≤ 1) {Y : ℝ} (hY : 0 ≤ Y) :
    ‖G t s h - ∫ v in (-Y)..Y, gauss t s h v‖ ≤
      2 * Real.exp (8 * t) * √(2 * π / (3 / (32 * t))) *
        Real.exp (-((3 / (32 * t)) / 2) * Y ^ 2) := by
  set c : ℝ := 3 / (32 * t) with hc
  have hc0 : 0 < c := by positivity
  have hint := integrable_gauss ht hs hst h
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hsplit : G t s h - ∫ v in Ioc (-Y) Y, gauss t s h v = ∫ v in (Ioc (-Y) Y)ᶜ, gauss t s h v := by
    have := integral_add_compl (measurableSet_Ioc (a := -Y) (b := Y)) hint
    unfold G
    linear_combination this.symm
  rw [hsplit]
  have hmaj : Integrable (fun v : ℝ => Real.exp (8 * t) * Real.exp (-c * v ^ 2)) :=
    (integrable_exp_neg_mul_sq hc0).const_mul _
  calc ‖∫ v in (Ioc (-Y) Y)ᶜ, gauss t s h v‖
      ≤ ∫ v in (Ioc (-Y) Y)ᶜ, Real.exp (8 * t) * Real.exp (-c * v ^ 2) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hmaj.integrableOn
        exact Eventually.of_forall fun v => norm_gauss_le' ht hs hst hq v
    _ ≤ ∫ v in Iic (-Y) ∪ Ioi Y, Real.exp (8 * t) * Real.exp (-c * v ^ 2) := by
        apply setIntegral_mono_set hmaj.integrableOn
          (Eventually.of_forall fun v => by positivity)
        refine Eventually.of_forall fun v => ?_
        show v ∈ (Ioc (-Y) Y)ᶜ → v ∈ Iic (-Y) ∪ Ioi Y
        intro hv
        simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hv
        simp only [mem_union, mem_Iic, mem_Ioi]
        exact hv
    _ = (∫ v in Iic (-Y), Real.exp (8 * t) * Real.exp (-c * v ^ 2)) +
          ∫ v in Ioi Y, Real.exp (8 * t) * Real.exp (-c * v ^ 2) := by
        apply setIntegral_union (Set.disjoint_left.mpr fun v h1 h2 => by
          simp only [mem_Iic] at h1
          simp only [mem_Ioi] at h2
          linarith) measurableSet_Ioi hmaj.integrableOn hmaj.integrableOn
    _ = 2 * ∫ v in Ioi Y, Real.exp (8 * t) * Real.exp (-c * v ^ 2) := by
        have hsym : (∫ v in Iic (-Y), Real.exp (8 * t) * Real.exp (-c * v ^ 2)) =
            ∫ v in Ioi Y, Real.exp (8 * t) * Real.exp (-c * v ^ 2) := by
          have := integral_comp_neg_Iic (-Y) (fun v : ℝ => Real.exp (8 * t) * Real.exp (-c * v ^ 2))
          rw [neg_neg] at this
          rw [← this]
          apply setIntegral_congr_fun measurableSet_Iic
          intro v _
          simp only
          ring_nf
        rw [hsym]
        ring
    _ ≤ 2 * (Real.exp (8 * t) * (√(2 * π / c) * Real.exp (-(c / 2) * Y ^ 2))) := by
        rw [MeasureTheory.integral_const_mul]
        gcongr
        exact gaussian_tail hc0 hY
    _ = _ := by ring

theorem cube_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

/-- **The defect integral on the window.** -/
theorem norm_window_defect_le {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 2 ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖)
    {h : ℝ} (hh : 0 ≤ h) (hq : ‖q s h‖ ≤ 1) {Y : ℝ} (hY : 0 ≤ Y)
    (hgood : ∀ v : ℝ, |v| ≤ Y → GoodSeg s (h + Complex.I * v))
    (hζ : ∀ v : ℝ, |v| ≤ Y → ‖(h : ℂ) + Complex.I * v‖ ≤ ‖s‖ / 8)
    (hsmall : 402 * (h + Y) ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) ≤ 1) :
    ‖∫ v in (-Y)..Y, gauss t s h v * D t s h v‖ ≤
      2 * Real.exp (8 * t) *
        ((1608 * h ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) * √(π / (3 / (32 * t))) +
          1608 / ‖s‖ ^ 2 * (7 * (3 / (32 * t)) ^ (-(3 / 2 : ℝ)) * √(π / (3 * (3 / (32 * t)) / 4)))) := by
  set c : ℝ := 3 / (32 * t) with hc
  have hc0 : 0 < c := by positivity
  have hs0 : 0 < ‖s‖ := by linarith
  -- the pointwise majorant
  set m : ℝ → ℝ := fun v => 2 * Real.exp (8 * t) * Real.exp (-c * v ^ 2) *
    (1608 * h ^ 3 / ‖s‖ ^ 2 + 1608 * |v| ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) with hm
  have hm_nonneg : ∀ v, 0 ≤ m v := fun v => by rw [hm]; positivity
  have hpt : ∀ v : ℝ, |v| ≤ Y → ‖gauss t s h v * D t s h v‖ ≤ m v := by
    intro v hv
    rw [norm_mul, hm]
    have hn : ‖(h : ℂ) + Complex.I * v‖ ≤ h + |v| := by
      calc ‖(h : ℂ) + Complex.I * v‖ ≤ ‖(h : ℂ)‖ + ‖Complex.I * v‖ := norm_add_le _ _
        _ = h + |v| := by simp [abs_of_nonneg hh]
    have hn3 : ‖(h : ℂ) + Complex.I * v‖ ^ 3 ≤ (h + Y) ^ 3 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      linarith
    have hsmall' : 402 * ‖(h : ℂ) + Complex.I * v‖ ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) ≤ 1 := by
      refine le_trans ?_ hsmall
      gcongr
    have hD := norm_D_le ht (hgood v hv) hs (hζ v hv) hsmall'
    have hg := norm_gauss_le' ht hs hst hq v
    have hcube : ‖(h : ℂ) + Complex.I * v‖ ^ 3 ≤ 4 * (h ^ 3 + |v| ^ 3) := by
      calc ‖(h : ℂ) + Complex.I * v‖ ^ 3 ≤ (h + |v|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hn 3
        _ ≤ 4 * (h ^ 3 + |v| ^ 3) := cube_add_le hh (abs_nonneg v)
    calc ‖gauss t s h v‖ * ‖D t s h v‖
        ≤ (Real.exp (8 * t) * Real.exp (-c * v ^ 2)) *
            (2 * (402 * ‖(h : ℂ) + Complex.I * v‖ ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖))) := by
          gcongr
      _ ≤ (Real.exp (8 * t) * Real.exp (-c * v ^ 2)) *
            (2 * (402 * (4 * (h ^ 3 + |v| ^ 3)) / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖))) := by
          gcongr
      _ = 2 * Real.exp (8 * t) * Real.exp (-c * v ^ 2) *
            (1608 * h ^ 3 / ‖s‖ ^ 2 + 1608 * |v| ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) := by
          ring
  have hmint : Integrable m := by
    rw [hm]
    have h1 := (integrable_exp_neg_mul_sq hc0).const_mul
      (2 * Real.exp (8 * t) * (1608 * h ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)))
    have h2 := (integrable_majorant hc0).const_mul (2 * Real.exp (8 * t) * (1608 / ‖s‖ ^ 2))
    refine (h1.add h2).congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply]
    ring
  have hI3 : ∫ v : ℝ, |v| ^ 3 * Real.exp (-c * v ^ 2) ≤
      7 * c ^ (-(3 / 2 : ℝ)) * √(π / (3 * c / 4)) := by
    calc ∫ v : ℝ, |v| ^ 3 * Real.exp (-c * v ^ 2)
        ≤ ∫ v : ℝ, 7 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(3 * c / 4) * v ^ 2) := by
          apply integral_mono (integrable_majorant hc0)
            ((integrable_exp_neg_mul_sq (by positivity)).const_mul _)
          intro v
          exact cube_mul_exp_le' hc0 v
      _ = 7 * c ^ (-(3 / 2 : ℝ)) * √(π / (3 * c / 4)) := by
          rw [MeasureTheory.integral_const_mul, integral_gaussian]
  have hm_eval : ∫ v : ℝ, m v =
      2 * Real.exp (8 * t) * ((1608 * h ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) * √(π / c) +
        1608 / ‖s‖ ^ 2 * ∫ v : ℝ, |v| ^ 3 * Real.exp (-c * v ^ 2)) := by
    have h1 := (integrable_exp_neg_mul_sq hc0).const_mul
      (2 * Real.exp (8 * t) * (1608 * h ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)))
    have h2 := (integrable_majorant hc0).const_mul (2 * Real.exp (8 * t) * (1608 / ‖s‖ ^ 2))
    have hsplit : ∫ v : ℝ, m v =
        (∫ v : ℝ, 2 * Real.exp (8 * t) * (1608 * h ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) *
          Real.exp (-c * v ^ 2)) +
        ∫ v : ℝ, 2 * Real.exp (8 * t) * (1608 / ‖s‖ ^ 2) * (|v| ^ 3 * Real.exp (-c * v ^ 2)) := by
      rw [← integral_add h1 h2]
      apply integral_congr_ae
      refine Eventually.of_forall fun v => ?_
      simp only [hm]
      ring
    rw [hsplit, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, integral_gaussian]
    ring
  calc ‖∫ v in (-Y)..Y, gauss t s h v * D t s h v‖
      ≤ ∫ v in (-Y)..Y, m v := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ hmint.intervalIntegrable
        refine Eventually.of_forall fun v hv => ?_
        apply hpt
        rw [abs_le]
        exact ⟨hv.1.le, hv.2⟩
    _ ≤ ∫ v : ℝ, m v := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hmint (Eventually.of_forall hm_nonneg)
    _ ≤ _ := by
        rw [hm_eval]
        gcongr

end Soma.Holonics.RH.EventWindow
