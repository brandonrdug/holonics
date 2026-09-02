import ElementaryHolonics.RH.GammaGrowth
import ElementaryHolonics.RH.HeatFlowEntire
import ElementaryHolonics.RH.RiemannXi
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# The growth bound for `Ξ`: order one, in the form `‖Ξ s‖ ≤ A exp (B ‖s‖^{3/2})`

`completedRiemannZeta₀ s = Λ₀(s/2)/2` with `Λ₀ = mellin f_modif` for the theta kernel pair.
The modified kernel on `(0, ∞)` is `h t + t^{−1/2} h(1/t)` with `h = 1_{(1,∞)} (θ − 1)`, and
`‖h t‖ ≤ Cθ e^{−πt}` from the explicit Jacobi theta bound.  Each Mellin piece is then bounded by
`Cθ · G(Re)` with the incomplete Gamma envelope `G`, which gives
`‖Ξ s‖ ≤ (Cθ e^{74} + 1) exp (10 ‖s‖^{3/2})`.  Since `3/2 < 2`, the derivative-series heat flow
of `Ξ` is an entire function for every real `t`: `H_t` exists at the entire-function face.
-/

open Complex Real MeasureTheory Set Filter HurwitzZeta
open Soma.Holonics.RH.GammaGrowth
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RiemannXi

namespace Soma.Holonics.RH.XiGrowth

/-- The theta kernel minus one, cut off to `(1, ∞)`. -/
noncomputable def h (t : ℝ) : ℂ :=
  (Ioi 1).indicator (fun x : ℝ => ((evenKernel 0 x : ℝ) : ℂ) - 1) t

/-- The theta constant `2 / (1 − e^{−π})`. -/
noncomputable def Cθ : ℝ := 2 / (1 - rexp (-π))

theorem exp_neg_pi_lt_one : rexp (-π) < 1 := by
  have := Real.exp_lt_exp.mpr (by linarith [Real.pi_pos] : -π < 0)
  rwa [Real.exp_zero] at this

theorem Cθ_pos : 0 < Cθ := by
  unfold Cθ
  have := exp_neg_pi_lt_one
  exact div_pos (by norm_num) (by linarith)

theorem evenKernel_eq_jacobiTheta (x : ℝ) :
    ((evenKernel 0 x : ℝ) : ℂ) = jacobiTheta (I * x) := by
  have := evenKernel_def 0 x
  simp at this
  rw [this, jacobiTheta_eq_jacobiTheta₂]

theorem norm_evenKernel_sub_one_le {x : ℝ} (hx : 1 ≤ x) :
    ‖((evenKernel 0 x : ℝ) : ℂ) - 1‖ ≤ Cθ * rexp (-(π * x)) := by
  have hx0 : 0 < x := by linarith
  rw [evenKernel_eq_jacobiTheta]
  have h2 := norm_jacobiTheta_sub_one_le (τ := I * x) (by simpa using hx0)
  have him : (I * (x : ℂ)).im = x := by simp
  rw [him] at h2
  refine h2.trans ?_
  unfold Cθ
  have hpx : rexp (-π * x) ≤ rexp (-π) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have he1 := exp_neg_pi_lt_one
  rw [show -(π * x) = -π * x by ring]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

theorem integrable_majorant (a : ℝ) :
    Integrable (fun t : ℝ =>
      (Ioi 1).indicator (fun x => Cθ * (x ^ (a - 1) * rexp (-(π * x)))) t) :=
  IntegrableOn.integrable_indicator
    (show IntegrableOn (fun x : ℝ => Cθ * (x ^ (a - 1) * rexp (-(π * x)))) (Ioi 1) volume from
      (integrableOn_rpow_mul_exp a).const_mul Cθ) measurableSet_Ioi

theorem norm_term_le (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • h t‖ ≤
      (Ioi 1).indicator (fun x => Cθ * (x ^ (s.re - 1) * rexp (-(π * x)))) t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  unfold h
  by_cases h1 : t ∈ Ioi 1
  · rw [indicator_of_mem h1, indicator_of_mem h1]
    have := norm_evenKernel_sub_one_le (le_of_lt (mem_Ioi.mp h1))
    calc t ^ (s.re - 1) * ‖((evenKernel 0 t : ℝ) : ℂ) - 1‖
        ≤ t ^ (s.re - 1) * (Cθ * rexp (-(π * t))) :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht.le _)
      _ = Cθ * (t ^ (s.re - 1) * rexp (-(π * t))) := by ring
  · rw [indicator_of_notMem h1, indicator_of_notMem h1, norm_zero, mul_zero]

theorem aestronglyMeasurable_term (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) • h t) (volume.restrict (Ioi 0)) := by
  have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi 0) :=
    ContinuousOn.cpow_const continuous_ofReal.continuousOn
      (fun t ht => Complex.ofReal_mem_slitPlane.mpr ht)
  have h2 : AEStronglyMeasurable h (volume.restrict (Ioi 0)) := by
    unfold h
    apply AEStronglyMeasurable.indicator _ measurableSet_Ioi
    exact ((continuous_ofReal.comp_continuousOn (continuousOn_evenKernel 0)).sub
      continuousOn_const).aestronglyMeasurable measurableSet_Ioi
  exact (h1.aestronglyMeasurable measurableSet_Ioi).smul h2

theorem mellinConvergent_h (s : ℂ) : MellinConvergent h s := by
  unfold MellinConvergent
  refine (integrable_majorant s.re).integrableOn.mono' (aestronglyMeasurable_term s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_term_le s ht

/-- The Mellin transform of the cut-off theta kernel is bounded by the Gamma envelope. -/
theorem norm_mellin_h_le (s : ℂ) : ‖mellin h s‖ ≤ Cθ * G s.re := by
  unfold mellin
  have hint := (integrable_majorant s.re).integrableOn (s := Ioi 0)
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_term_le s ht
  · have hI : Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 := inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hI,
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_rpow_mul_exp_le_G s.re) Cθ_pos.le

/-- The modified theta kernel on `(0, ∞)` is `h t + t^{−1/2} h (1/t)`. -/
theorem f_modif_eq {t : ℝ} (ht : 0 < t) :
    (hurwitzEvenFEPair 0).f_modif t = h t + (t : ℂ) ^ (-(1 / 2 : ℂ)) • h t⁻¹ := by
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Pi.add_apply, Function.comp, if_pos]
  unfold h
  rcases lt_trichotomy t 1 with h1 | h1 | h1
  · have ht1 : t ∉ Ioi 1 := by simp [h1.le]
    have ht2 : t ∈ Ioo 0 1 := ⟨ht, h1⟩
    have ht3 : t⁻¹ ∈ Ioi 1 := mem_Ioi.mpr (one_lt_inv_iff₀.mpr ⟨ht, h1⟩)
    rw [indicator_of_notMem ht1, indicator_of_mem ht2, indicator_of_mem ht3]
    have hFE : evenKernel 0 t = t ^ (-(1 / 2 : ℝ)) * evenKernel 0 t⁻¹ := by
      rw [evenKernel_functional_equation 0 t, evenKernel_eq_cosKernel_of_zero,
        one_div (t ^ (1 / 2 : ℝ)), one_div t, Real.rpow_neg ht.le]
    have hc : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]
      norm_num
    rw [hc, hFE]
    push_cast
    simp only [smul_eq_mul]
    ring
  · subst h1
    simp
  · have ht1 : t ∈ Ioi 1 := mem_Ioi.mpr h1
    have ht2 : t ∉ Ioo 0 1 := fun h => absurd h.2 (not_lt.mpr h1.le)
    have ht3 : t⁻¹ ∉ Ioi 1 := by
      rw [mem_Ioi, not_lt]
      exact (inv_lt_one_of_one_lt₀ h1).le
    rw [indicator_of_mem ht1, indicator_of_notMem ht2, indicator_of_notMem ht3, smul_zero,
      add_zero]

theorem mellinConvergent_second (s : ℂ) :
    MellinConvergent (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • h t⁻¹) s := by
  rw [MellinConvergent.cpow_smul]
  have : (fun t : ℝ => h t⁻¹) = fun t => h (t ^ (-1 : ℝ)) := by
    funext t
    rw [Real.rpow_neg_one]
  rw [this, MellinConvergent.comp_rpow (by norm_num)]
  exact mellinConvergent_h _

theorem mellin_second (s : ℂ) :
    mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • h t⁻¹) s = mellin h (1 / 2 - s) := by
  rw [mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

/-- `Λ₀` of the theta pair is bounded by the two Gamma envelopes. -/
theorem norm_Λ₀_le (s : ℂ) :
    ‖(hurwitzEvenFEPair 0).Λ₀ s‖ ≤ Cθ * (G s.re + G (1 / 2 - s.re)) := by
  have hdecomp : (hurwitzEvenFEPair 0).Λ₀ s = mellin h s + mellin h (1 / 2 - s) := by
    unfold WeakFEPair.Λ₀
    have heq : mellin (hurwitzEvenFEPair 0).f_modif s =
        mellin (fun t : ℝ => h t + (t : ℂ) ^ (-(1 / 2 : ℂ)) • h t⁻¹) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [f_modif_eq ht]
    have hadd := (hasMellin_add (mellinConvergent_h s) (mellinConvergent_second s)).2
    rw [heq, hadd, mellin_second]
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_mellin_h_le s
  have h2 := norm_mellin_h_le (1 / 2 - s)
  have h3 : (1 / 2 - s : ℂ).re = 1 / 2 - s.re := by simp
  rw [h3] at h2
  linarith

theorem norm_completedRiemannZeta₀_le (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤ Cθ * (G (s.re / 2) + G (1 / 2 - s.re / 2)) / 2 := by
  have h0 : completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 := rfl
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h0, norm_div, h2]
  have := norm_Λ₀_le (s / 2)
  have hre : (s / 2).re = s.re / 2 := by simp
  rw [hre] at this
  exact div_le_div_of_nonneg_right this (by norm_num)

theorem G_le_of_abs_le {a r : ℝ} (hr : 0 ≤ r) (ha : |a| ≤ r + 1) :
    G a ≤ rexp (8 * r ^ (3 / 2 : ℝ) + 72) := by
  unfold G
  apply Real.exp_le_exp.mpr
  have h1 : (|a| + 2) ^ (3 / 2 : ℝ) ≤ (r + 3) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h2 : (r + 3) ^ (3 / 2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) * (r ^ (3 / 2 : ℝ) + 3 ^ (3 / 2 : ℝ)) :=
    add_rpow_le (by norm_num) hr (by norm_num)
  have h3 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    calc (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have h4 : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 9 := by
    calc (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 9 := by rw [Real.rpow_two]; norm_num
  have h5 : 0 ≤ r ^ (3 / 2 : ℝ) := Real.rpow_nonneg hr _
  have h6 : (2 : ℝ) ^ (3 / 2 : ℝ) * (r ^ (3 / 2 : ℝ) + 3 ^ (3 / 2 : ℝ)) ≤
      4 * (r ^ (3 / 2 : ℝ) + 9) :=
    mul_le_mul h3 (by linarith) (by positivity) (by norm_num)
  linarith

/-- `‖completedRiemannZeta₀ s‖ ≤ Cθ exp (8 ‖s‖^{3/2} + 72)`. -/
theorem norm_completedRiemannZeta₀_le' (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤ Cθ * rexp (8 * ‖s‖ ^ (3 / 2 : ℝ) + 72) := by
  refine (norm_completedRiemannZeta₀_le s).trans ?_
  have hre := abs_le.mp (Complex.abs_re_le_norm s)
  have hn := norm_nonneg s
  have hG1 : G (s.re / 2) ≤ rexp (8 * ‖s‖ ^ (3 / 2 : ℝ) + 72) := by
    apply G_le_of_abs_le (norm_nonneg s)
    rw [abs_le]
    constructor <;> linarith [hre.1, hre.2]
  have hG2 : G (1 / 2 - s.re / 2) ≤ rexp (8 * ‖s‖ ^ (3 / 2 : ℝ) + 72) := by
    apply G_le_of_abs_le (norm_nonneg s)
    rw [abs_le]
    constructor <;> linarith [hre.1, hre.2]
  calc Cθ * (G (s.re / 2) + G (1 / 2 - s.re / 2)) / 2
      ≤ Cθ * (rexp (8 * ‖s‖ ^ (3 / 2 : ℝ) + 72) + rexp (8 * ‖s‖ ^ (3 / 2 : ℝ) + 72)) / 2 := by
        gcongr
        exact Cθ_pos.le
    _ = Cθ * rexp (8 * ‖s‖ ^ (3 / 2 : ℝ) + 72) := by ring

/-- The growth bound for `Ξ`: `‖Ξ s‖ ≤ (Cθ e^{74} + 1) exp (10 ‖s‖^{3/2})`. -/
theorem norm_riemannXi_le (s : ℂ) :
    ‖riemannXi s‖ ≤ (Cθ * rexp 74 + 1) * rexp (10 * ‖s‖ ^ (3 / 2 : ℝ)) := by
  unfold riemannXi
  set X := ‖s‖ ^ (3 / 2 : ℝ) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg (norm_nonneg s) _
  have hsX : ‖s‖ ≤ X + 1 := by
    rcases le_or_gt ‖s‖ 1 with h | h
    · linarith
    · calc ‖s‖ = ‖s‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖s‖ ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
        _ ≤ X + 1 := by linarith
  have hΛ := norm_completedRiemannZeta₀_le' s
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, h2]
  have hs1 : ‖s - 1‖ ≤ ‖s‖ + 1 := (norm_sub_le _ _).trans (by simp)
  have hE : 0 ≤ Cθ * rexp (8 * X + 72) := (mul_pos Cθ_pos (Real.exp_pos _)).le
  have hnum : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ ≤
      ‖s‖ * (‖s‖ + 1) * (Cθ * rexp (8 * X + 72)) + 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_one]
    gcongr
  have hpoly : ‖s‖ * (‖s‖ + 1) ≤ rexp (2 * X + 2) := by
    have h1 : ‖s‖ + 1 ≤ rexp ‖s‖ := Real.add_one_le_exp _
    have h2 : ‖s‖ * (‖s‖ + 1) ≤ (‖s‖ + 1) * (‖s‖ + 1) := by nlinarith [norm_nonneg s]
    have h3 : (‖s‖ + 1) * (‖s‖ + 1) ≤ rexp ‖s‖ * rexp ‖s‖ :=
      mul_le_mul h1 h1 (by linarith [norm_nonneg s]) (Real.exp_pos _).le
    have h4 : rexp ‖s‖ * rexp ‖s‖ = rexp (2 * ‖s‖) := by
      rw [← Real.exp_add]
      ring_nf
    have h5 : rexp (2 * ‖s‖) ≤ rexp (2 * X + 2) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have he : rexp (2 * X + 2) * (Cθ * rexp (8 * X + 72)) = Cθ * rexp 74 * rexp (10 * X) := by
    rw [mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    ring_nf
  have h1 : 1 ≤ rexp (10 * X) := Real.one_le_exp (by linarith)
  have hpos : 0 ≤ Cθ * rexp 74 * rexp (10 * X) :=
    mul_nonneg (mul_nonneg Cθ_pos.le (Real.exp_pos _).le) (Real.exp_pos _).le
  calc ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ / 2
      ≤ (rexp (2 * X + 2) * (Cθ * rexp (8 * X + 72)) + 1) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        refine hnum.trans ?_
        exact add_le_add (mul_le_mul_of_nonneg_right hpoly hE) le_rfl
    _ = (Cθ * rexp 74 * rexp (10 * X) + 1) / 2 := by rw [he]
    _ ≤ (Cθ * rexp 74 + 1) * rexp (10 * X) := by nlinarith

/-- `Ξ` has growth of order `3/2 < 2`. -/
theorem hasGrowth_riemannXi : HasGrowth riemannXi (Cθ * rexp 74 + 1) 10 (3 / 2) :=
  fun s => norm_riemannXi_le s

theorem A_nonneg : 0 ≤ Cθ * rexp 74 + 1 := (add_pos (mul_pos Cθ_pos (Real.exp_pos _)) one_pos).le

/-- The heat series of `Ξ` converges absolutely at every point for every real `t`. -/
theorem summable_heatTerm_riemannXi (t : ℝ) (z : ℂ) :
    Summable (fun k => ‖heatTerm t riemannXi z k‖) :=
  summable_heatTerm differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num) t z

/-- `H_t = e^{−tD²} Ξ` is an entire function for every real `t`. -/
theorem differentiable_heatE_riemannXi (t : ℝ) : Differentiable ℂ (heatE t riemannXi) :=
  differentiable_heatE differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num) t

end Soma.Holonics.RH.XiGrowth
