import Mathlib
import ElementaryHolonics.RH.EventPieces

/-!
# RT3 (iii-h): the tails of the line `Re z = 2`

On `Re z = 2`, `‖f(2 + iy')‖ ≤ K₀ e^{−(y' − Im w)²/(4t)} (1 + |y'|)` with
`K₀ = e^{(2 − Re w)²/(4t)}/(2π)`. Outside the window `|y' − y| ≤ Y` with `|Im w − y| ≤ tπ` and
`Y ≥ 2tπ`, the Gaussian is at most `e^{−(y'−y)²/(16t)}`, so the two tails together are at most
`2 K₀ (1 + |y| + 4√t) √(64πt) e^{−Y²/(64t)}`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventTail

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.EventSaddle
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventWindow

/-- `|u| e^{−c u²} ≤ c^{−1/2} e^{−c u²/2}`. -/
theorem abs_mul_exp_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    |u| * Real.exp (-c * u ^ 2) ≤ (√c)⁻¹ * Real.exp (-(c / 2) * u ^ 2) := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  have hx : √c * |u| ≤ Real.exp (c * u ^ 2 / 2) := by
    have h1 : √c * |u| ≤ 1 + (√c * |u|) ^ 2 / 2 := by nlinarith [sq_nonneg (√c * |u| - 1)]
    have h2 : (√c * |u|) ^ 2 = c * u ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le, sq_abs]
    have h3 : 1 + c * u ^ 2 / 2 ≤ Real.exp (c * u ^ 2 / 2) := by
      linarith [Real.add_one_le_exp (c * u ^ 2 / 2)]
    rw [h2] at h1
    linarith
  calc |u| * Real.exp (-c * u ^ 2) = (√c)⁻¹ * ((√c * |u|) * Real.exp (-c * u ^ 2)) := by
        field_simp
    _ ≤ (√c)⁻¹ * (Real.exp (c * u ^ 2 / 2) * Real.exp (-c * u ^ 2)) := by gcongr
    _ = (√c)⁻¹ * Real.exp (-(c / 2) * u ^ 2) := by
        rw [← Real.exp_add]
        congr 2
        ring

theorem integrable_abs_mul_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => |u| * Real.exp (-c * u ^ 2)) := by
  have hg := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < c / 2)).const_mul (√c)⁻¹
  refine hg.mono' ?_ (Eventually.of_forall fun u => ?_)
  · exact (continuous_abs.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact abs_mul_exp_le hc u

/-- The pointwise bound on the line `Re z = 2`. -/
theorem norm_f_two_le {t : ℝ} (ht : 0 < t) (w : ℂ) (y' : ℝ) :
    ‖f t w (2 + Complex.I * y')‖ ≤
      Real.exp ((2 - w.re) ^ 2 / (4 * t)) / (2 * π) *
        (Real.exp (-((y' - w.im) ^ 2) / (4 * t)) * (1 + |y'|)) := by
  rw [f_apply, norm_mul, Complex.norm_exp]
  have hre : (((2 : ℂ) + Complex.I * y' - w) ^ 2 / (4 * t)).re =
      ((2 - w.re) ^ 2 - (y' - w.im) ^ 2) / (4 * t) := by
    have e : ((2 : ℂ) + Complex.I * y' - w) = ((2 - w.re : ℝ) : ℂ) + ((y' - w.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [e]
    have h4 : (4 * (t : ℂ)) = ((4 * t : ℝ) : ℂ) := by push_cast; ring
    rw [h4, Complex.div_ofReal_re]
    simp [sq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
  rw [hre]
  have h2 := norm_γ₁_two y'
  calc Real.exp (((2 - w.re) ^ 2 - (y' - w.im) ^ 2) / (4 * t)) * ‖Soma.Holonics.RH.FlowedGammaContour.γ₁ (2 + Complex.I * y')‖
      ≤ Real.exp (((2 - w.re) ^ 2 - (y' - w.im) ^ 2) / (4 * t)) * ((1 + |y'|) / (2 * π)) := by
        gcongr
    _ = _ := by
        rw [show ((2 - w.re) ^ 2 - (y' - w.im) ^ 2) / (4 * t) =
          (2 - w.re) ^ 2 / (4 * t) + -((y' - w.im) ^ 2) / (4 * t) by ring, Real.exp_add]
        ring

/-- `f` is differentiable on `Re z > −2`. -/
theorem differentiableAt_f_of_re {t : ℝ} (w : ℂ) {z : ℂ} (hz : -2 < z.re) :
    DifferentiableAt ℂ (f t w) z := by
  have : f t w = fun z => Complex.exp ((z - w) ^ 2 / (4 * t)) *
      Soma.Holonics.RH.FlowedGammaContour.γ₁ z := funext (f_apply t w)
  rw [this]
  exact (((differentiableAt_id.sub_const w).pow 2).div_const _).cexp.mul
    (Soma.Holonics.RH.FlowedGammaContour.differentiableAt_γ₁ hz)

theorem continuous_f_two {t : ℝ} (w : ℂ) : Continuous fun y' : ℝ => f t w (2 + Complex.I * y') := by
  apply continuous_iff_continuousAt.mpr
  intro y'
  have h1 : DifferentiableAt ℂ (f t w) (2 + Complex.I * y') :=
    differentiableAt_f_of_re w (by simp <;> norm_num)
  exact ContinuousAt.comp (g := f t w) (f := fun y' : ℝ => (2 : ℂ) + Complex.I * y') h1.continuousAt
    (by fun_prop : Continuous fun y' : ℝ => (2 : ℂ) + Complex.I * y').continuousAt

/-- The even majorant `M(u) = K₀ e^{−u²/(16t)} (1 + |y| + |u|)`. -/
def M (t : ℝ) (K₀ y : ℝ) (u : ℝ) : ℝ := K₀ * (Real.exp (-(1 / (16 * t)) * u ^ 2) * (1 + |y| + |u|))

theorem integrable_M {t : ℝ} (ht : 0 < t) (K₀ y : ℝ) : Integrable (M t K₀ y) := by
  have hc : (0 : ℝ) < 1 / (16 * t) := by positivity
  have h1 := (integrable_exp_neg_mul_sq hc).const_mul (1 + |y|)
  have h2 := integrable_abs_mul_gauss hc
  refine ((h1.add h2).const_mul K₀).congr (Eventually.of_forall fun u => ?_)
  unfold M
  simp only [Pi.add_apply]
  ring

theorem M_nonneg {t : ℝ} {K₀ : ℝ} (hK : 0 ≤ K₀) (y u : ℝ) : 0 ≤ M t K₀ y u := by
  unfold M
  positivity

theorem M_neg {t : ℝ} (K₀ y u : ℝ) : M t K₀ y (-u) = M t K₀ y u := by
  unfold M
  simp

/-- The half-line integral of the majorant. -/
theorem integral_Ioi_M_le {t : ℝ} (ht : 0 < t) {K₀ : ℝ} (hK : 0 ≤ K₀) (y : ℝ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ u in Ioi Y, M t K₀ y u ≤
      K₀ * (1 + |y| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t))) := by
  set c : ℝ := 1 / (16 * t) with hc
  have hc0 : 0 < c := by positivity
  have hsc : √c = (4 * √t)⁻¹ := by
    rw [hc, one_div, Real.sqrt_inv, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16) t,
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpt : ∀ u, M t K₀ y u ≤ K₀ * ((1 + |y|) * Real.exp (-c * u ^ 2) +
      4 * √t * Real.exp (-(c / 2) * u ^ 2)) := by
    intro u
    unfold M
    have h := abs_mul_exp_le hc0 u
    rw [hsc, inv_inv] at h
    have : Real.exp (-c * u ^ 2) * (1 + |y| + |u|) =
        (1 + |y|) * Real.exp (-c * u ^ 2) + |u| * Real.exp (-c * u ^ 2) := by ring
    rw [this]
    gcongr
  have hI1 := gaussian_tail hc0 hY
  have hI2 := gaussian_tail (by positivity : (0 : ℝ) < c / 2) hY
  have hmaj : Integrable (fun u : ℝ => K₀ * ((1 + |y|) * Real.exp (-c * u ^ 2) +
      4 * √t * Real.exp (-(c / 2) * u ^ 2))) :=
    (((integrable_exp_neg_mul_sq hc0).const_mul _).add
      ((integrable_exp_neg_mul_sq (by positivity)).const_mul _)).const_mul _
  calc ∫ u in Ioi Y, M t K₀ y u
      ≤ ∫ u in Ioi Y, K₀ * ((1 + |y|) * Real.exp (-c * u ^ 2) +
          4 * √t * Real.exp (-(c / 2) * u ^ 2)) := by
        apply setIntegral_mono_on (integrable_M ht K₀ y).integrableOn hmaj.integrableOn
          measurableSet_Ioi
        intro u _
        exact hpt u
    _ = K₀ * ((1 + |y|) * (∫ u in Ioi Y, Real.exp (-c * u ^ 2)) +
          4 * √t * (∫ u in Ioi Y, Real.exp (-(c / 2) * u ^ 2))) := by
        rw [MeasureTheory.integral_const_mul,
          integral_add ((integrable_exp_neg_mul_sq hc0).const_mul (1 + |y|)).integrableOn
            ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < c / 2)).const_mul (4 * √t)).integrableOn,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ K₀ * ((1 + |y|) * (√(2 * π / c) * Real.exp (-(c / 2) * Y ^ 2)) +
          4 * √t * (√(2 * π / (c / 2)) * Real.exp (-(c / 2 / 2) * Y ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact add_le_add (mul_le_mul_of_nonneg_left (a := 1 + |y|) hI1 (by positivity))
          (mul_le_mul_of_nonneg_left (a := 4 * √t) hI2 (by positivity))
    _ ≤ K₀ * ((1 + |y|) * (√(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t)))) +
          4 * √t * (√(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t))))) := by
        have e1 : √(2 * π / c) ≤ √(64 * π * t) := by
          apply Real.sqrt_le_sqrt
          rw [hc]
          have : 2 * π / (1 / (16 * t)) = 32 * π * t := by field_simp; ring
          rw [this]
          nlinarith [Real.pi_pos]
        have e2 : √(2 * π / (c / 2)) = √(64 * π * t) := by
          congr 1
          rw [hc]
          field_simp
          ring
        have e3 : Real.exp (-(c / 2) * Y ^ 2) ≤ Real.exp (-(Y ^ 2 / (64 * t))) := by
          apply Real.exp_le_exp.mpr
          rw [hc]
          have : -(1 / (16 * t) / 2) * Y ^ 2 = -(Y ^ 2 / (32 * t)) := by field_simp; ring
          rw [this]
          have : Y ^ 2 / (64 * t) ≤ Y ^ 2 / (32 * t) := by
            apply div_le_div_of_nonneg_left (sq_nonneg Y) (by positivity)
            linarith
          linarith
        have e4 : Real.exp (-(c / 2 / 2) * Y ^ 2) = Real.exp (-(Y ^ 2 / (64 * t))) := by
          congr 1
          rw [hc]
          field_simp
          ring
        rw [e2, e4]
        gcongr
    _ = K₀ * (1 + |y| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t))) := by ring

/-- The chain from the pointwise majorant to the two Gaussian tails. -/
theorem tail_chain {t : ℝ} (ht : 0 < t) {K₀ : ℝ} (hK : 0 ≤ K₀) (y : ℝ) {Y : ℝ} (hY0 : 0 ≤ Y)
    (F : ℝ → ℂ) (hMint : Integrable (fun y' : ℝ => M t K₀ y (y' - y)))
    (hpt : ∀ y' : ℝ, y' ∈ (Ioc (y - Y) (y + Y))ᶜ → ‖F y'‖ ≤ M t K₀ y (y' - y)) :
    ‖(∫ y' in (Ioc (y - Y) (y + Y))ᶜ, F y')‖ ≤
      2 * (K₀ * (1 + |y| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t)))) := by
  calc ‖(∫ y' in (Ioc (y - Y) (y + Y))ᶜ, F y')‖
      ≤ ∫ y' in (Ioc (y - Y) (y + Y))ᶜ, M t K₀ y (y' - y) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hMint.integrableOn
        rw [ae_restrict_iff' (measurableSet_Ioc.compl)]
        exact Eventually.of_forall hpt
    _ = (∫ y' : ℝ, M t K₀ y (y' - y)) - ∫ y' in Ioc (y - Y) (y + Y), M t K₀ y (y' - y) := by
        have := integral_add_compl (measurableSet_Ioc (a := y - Y) (b := y + Y)) hMint
        linear_combination this
    _ = (∫ u : ℝ, M t K₀ y u) - ∫ u in Ioc (-Y) Y, M t K₀ y u := by
        rw [MeasureTheory.integral_sub_right_eq_self (M t K₀ y) y]
        congr 1
        rw [← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le (by linarith),
          intervalIntegral.integral_comp_sub_right (fun u => M t K₀ y u) y]
        congr 1 <;> ring
    _ = ∫ u in (Ioc (-Y) Y)ᶜ, M t K₀ y u := by
        have := integral_add_compl (measurableSet_Ioc (a := -Y) (b := Y)) (integrable_M ht K₀ y)
        linear_combination this.symm
    _ ≤ ∫ u in Iic (-Y) ∪ Ioi Y, M t K₀ y u := by
        apply setIntegral_mono_set (integrable_M ht K₀ y).integrableOn
          (Eventually.of_forall fun u => M_nonneg hK y u)
        refine Eventually.of_forall fun u => ?_
        show u ∈ (Ioc (-Y) Y)ᶜ → u ∈ Iic (-Y) ∪ Ioi Y
        intro hu
        simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hu
        simp only [mem_union, mem_Iic, mem_Ioi]
        exact hu
    _ = (∫ u in Iic (-Y), M t K₀ y u) + ∫ u in Ioi Y, M t K₀ y u := by
        apply setIntegral_union (Set.disjoint_left.mpr fun u h1 h2 => by
          simp only [mem_Iic] at h1
          simp only [mem_Ioi] at h2
          linarith) measurableSet_Ioi (integrable_M ht K₀ y).integrableOn
          (integrable_M ht K₀ y).integrableOn
    _ = 2 * ∫ u in Ioi Y, M t K₀ y u := by
        have hsym : (∫ u in Iic (-Y), M t K₀ y u) = ∫ u in Ioi Y, M t K₀ y u := by
          have := integral_comp_neg_Iic (-Y) (M t K₀ y)
          rw [neg_neg] at this
          rw [← this]
          apply setIntegral_congr_fun measurableSet_Iic
          intro u _
          exact (M_neg K₀ y u).symm
        rw [hsym]
        ring
    _ ≤ 2 * (K₀ * (1 + |y| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t)))) := by
        gcongr
        exact integral_Ioi_M_le ht hK y hY0


/-- The pointwise majorant on the complement of the window. -/
theorem norm_f_two_compl_le {t : ℝ} (ht : 0 < t) (w : ℂ) {y Y : ℝ} (hY : 2 * t * π ≤ Y)
    (hIm : |w.im - y| ≤ t * π) (y' : ℝ) (hy' : y' ∈ (Ioc (y - Y) (y + Y))ᶜ) :
    ‖f t w (2 + Complex.I * y')‖ ≤ M t (Real.exp ((2 - w.re) ^ 2 / (4 * t)) / (2 * π)) y (y' - y) := by
  have hY0 : 0 ≤ Y := by nlinarith [Real.pi_pos]
  simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hy'
  have hfar : Y ≤ |y' - y| := by
    rcases hy' with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  refine (norm_f_two_le ht w y').trans ?_
  unfold M
  have h1 : 1 + |y'| ≤ 1 + |y| + |y' - y| := by
    have := abs_sub (y' - y) (-y)
    rw [sub_neg_eq_add, sub_add_cancel, abs_neg] at this
    linarith
  have h2 : Real.exp (-((y' - w.im) ^ 2) / (4 * t)) ≤ Real.exp (-(1 / (16 * t)) * (y' - y) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h3 : |y' - y| / 2 ≤ |y' - w.im| := by
      have := abs_sub_abs_le_abs_sub (y' - y) (w.im - y)
      rw [show y' - y - (w.im - y) = y' - w.im by ring] at this
      have hπ : 0 < π := Real.pi_pos
      linarith
    have h4 : (y' - y) ^ 2 / 4 ≤ (y' - w.im) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h3 2
      rw [div_pow, sq_abs, sq_abs] at this
      linarith
    have e : -(1 / (16 * t)) * (y' - y) ^ 2 = -((y' - y) ^ 2 / 4) / (4 * t) := by
      field_simp
      ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  calc Real.exp ((2 - w.re) ^ 2 / (4 * t)) / (2 * π) *
        (Real.exp (-((y' - w.im) ^ 2) / (4 * t)) * (1 + |y'|))
      ≤ Real.exp ((2 - w.re) ^ 2 / (4 * t)) / (2 * π) *
        (Real.exp (-(1 / (16 * t)) * (y' - y) ^ 2) * (1 + |y| + |y' - y|)) := by gcongr

/-- **The two tails of the line `Re z = 2`.** -/
theorem norm_tail_le {t : ℝ} (ht : 0 < t) (w : ℂ) {y Y : ℝ} (hY : 2 * t * π ≤ Y)
    (hIm : |w.im - y| ≤ t * π) :
    ‖(∫ y' : ℝ, f t w (2 + Complex.I * y')) -
        (∫ y' in (y - Y)..(y + Y), f t w (2 + Complex.I * y'))‖ ≤
      2 * (Real.exp ((2 - w.re) ^ 2 / (4 * t)) / (2 * π)) * (1 + |y| + 4 * √t) * √(64 * π * t) *
        Real.exp (-(Y ^ 2 / (64 * t))) := by
  have hY0 : 0 ≤ Y := by nlinarith [Real.pi_pos]
  set K₀ : ℝ := Real.exp ((2 - w.re) ^ 2 / (4 * t)) / (2 * π) with hK₀
  have hK : 0 ≤ K₀ := by positivity
  set F : ℝ → ℂ := fun y' => f t w (2 + Complex.I * y') with hF
  -- integrability of F
  have hFint : Integrable F := by
    have hc : (0 : ℝ) < 1 / (4 * t) := by positivity
    have hmaj : Integrable (fun y' : ℝ => K₀ * (Real.exp (-(1 / (4 * t)) * (y' - w.im) ^ 2) *
        (1 + |w.im| + |y' - w.im|))) := by
      have := (integrable_M (t := t / 4) (by positivity) K₀ w.im).comp_sub_right w.im
      refine this.congr (Eventually.of_forall fun y' => ?_)
      unfold M
      simp only
      congr 3
      field_simp
      ring
    refine hmaj.mono' (continuous_f_two w).aestronglyMeasurable (Eventually.of_forall fun y' => ?_)
    rw [hF]
    simp only
    refine (norm_f_two_le ht w y').trans ?_
    rw [hK₀]
    have h1 : 1 + |y'| ≤ 1 + |w.im| + |y' - w.im| := by
      have := abs_sub (y' - w.im) (-w.im)
      rw [sub_neg_eq_add, sub_add_cancel, abs_neg] at this
      linarith
    have h2 : Real.exp (-((y' - w.im) ^ 2) / (4 * t)) = Real.exp (-(1 / (4 * t)) * (y' - w.im) ^ 2) := by
      congr 1
      ring
    rw [h2]
    gcongr
  -- the tail as the complement integral
  have hsplit : (∫ y' : ℝ, F y') - (∫ y' in (y - Y)..(y + Y), F y') =
      (∫ y' in (Ioc (y - Y) (y + Y))ᶜ, F y') := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    have := integral_add_compl (measurableSet_Ioc (a := y - Y) (b := y + Y)) hFint
    linear_combination this.symm
  show ‖(∫ y' : ℝ, F y') - (∫ y' in (y - Y)..(y + Y), F y')‖ ≤ _
  rw [hsplit]
  -- the majorant on the complement
  have hMint : Integrable (fun y' : ℝ => M t K₀ y (y' - y)) := by
    exact (integrable_M ht K₀ y).comp_sub_right y
  have hpt : ∀ y' : ℝ, y' ∈ (Ioc (y - Y) (y + Y))ᶜ → ‖F y'‖ ≤ M t K₀ y (y' - y) :=
    fun y' hy' => norm_f_two_compl_le ht w hY hIm y' hy'
  have hchain := tail_chain ht hK y hY0 F hMint hpt
  calc ‖(∫ y' in (Ioc (y - Y) (y + Y))ᶜ, F y')‖
      ≤ 2 * (K₀ * (1 + |y| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t)))) := hchain
    _ = _ := by rw [hK₀]; ring

end Soma.Holonics.RH.EventTail
