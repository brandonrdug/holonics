import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Growth of the Gamma function and of the incomplete Gamma integral

`Γ(b) ≤ exp (2 (b+1)^{3/2})` for `b ≥ 1`, through `Γ(b) ≤ Γ(⌈b⌉) = (⌈b⌉−1)! ≤ (b+1)^{b+1}` and
`log y ≤ 2 √y`.  Hence `∫_1^∞ t^{a−1} e^{−πt} dt ≤ Γ(max a 1) ≤ exp (2 (|a|+2)^{3/2})` for every
real `a`.  This is the archimedean growth that bounds `Ξ` to order one.
-/

open Real MeasureTheory Set Filter

namespace Soma.Holonics.RH.GammaGrowth

theorem Gamma_le_two_of_mem {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) : Gamma b ≤ 2 := by
  have hb0 : b ≠ 0 := by linarith
  have h1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one hb0
  have h3 : Gamma 3 = 2 := by
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Gamma_nat_eq_factorial]
    norm_num
  have h2 : Gamma (b + 1) ≤ Gamma 3 := by
    rcases eq_or_lt_of_le hb2 with h | h
    · rw [h]
      norm_num
    · exact (Gamma_strictMonoOn_Ici (by simp only [mem_Ici]; linarith)
        (by simp only [mem_Ici]; norm_num) (by linarith)).le
  have hpos := Gamma_pos_of_pos (by linarith : 0 < b)
  nlinarith

theorem Gamma_le_rpow {b : ℝ} (hb : 2 ≤ b) : Gamma b ≤ (b + 1) ^ (b + 1) := by
  set n := ⌈b⌉₊ with hn
  have hbn : b ≤ n := Nat.le_ceil b
  have hn1 : (n : ℝ) < b + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn2 : 2 ≤ n := by exact_mod_cast (le_trans hb hbn)
  have h1 : Gamma b ≤ Gamma n := by
    rcases eq_or_lt_of_le hbn with h | h
    · rw [h]
    · exact (Gamma_strictMonoOn_Ici (by simpa using hb) (by simpa using (le_trans hb hbn)) h).le
  have h2 : Gamma n = ((n - 1).factorial : ℝ) := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm]
    push_cast
    rw [Gamma_nat_eq_factorial]
  have h3 : (n - 1).factorial ≤ n ^ n :=
    (Nat.factorial_le_pow _).trans ((Nat.pow_le_pow_left (Nat.sub_le n 1) _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le n 1)))
  have h3' : ((n - 1).factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast h3
  have h4 : (n : ℝ) ^ n ≤ (b + 1) ^ (b + 1) := by
    rw [← Real.rpow_natCast]
    calc (n : ℝ) ^ (n : ℝ) ≤ (b + 1) ^ (n : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg n) hn1.le (Nat.cast_nonneg n)
      _ ≤ (b + 1) ^ (b + 1) := Real.rpow_le_rpow_of_exponent_le (by linarith) hn1.le
  linarith

theorem rpow_self_le_exp {b : ℝ} (hb : 0 ≤ b) :
    (b + 1) ^ (b + 1) ≤ exp (2 * (b + 1) ^ (3 / 2 : ℝ)) := by
  rw [Real.rpow_def_of_pos (by linarith)]
  apply exp_le_exp.mpr
  have hlog : log (b + 1) ≤ (b + 1) ^ (1 / 2 : ℝ) / (1 / 2) :=
    log_le_rpow_div (by linarith) (by norm_num)
  have h32 : (b + 1) ^ (3 / 2 : ℝ) = (b + 1) ^ (1 / 2 : ℝ) * (b + 1) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  rw [h32]
  have h2 : (b + 1) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (b + 1) ^ (1 / 2 : ℝ) := by ring
  rw [h2] at hlog
  have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ b + 1)
  linarith

/-- `Γ(b) ≤ exp (2 (b+1)^{3/2})` for `b ≥ 1`. -/
theorem Gamma_le_exp {b : ℝ} (hb : 1 ≤ b) : Gamma b ≤ exp (2 * (b + 1) ^ (3 / 2 : ℝ)) := by
  rcases le_or_gt b 2 with h | h
  · have h1 : (1 : ℝ) ≤ (b + 1) ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have := Real.add_one_le_exp (2 * (b + 1) ^ (3 / 2 : ℝ))
    linarith [Gamma_le_two_of_mem hb h]
  · exact (Gamma_le_rpow h.le).trans (rpow_self_le_exp (by linarith))

/-- Pointwise domination of `t^{a−1} e^{−πt}` by the Gamma integrand on `t > 1`. -/
theorem rpow_mul_exp_le {a t : ℝ} (ht : 1 < t) :
    t ^ (a - 1) * exp (-(π * t)) ≤ exp (-t) * t ^ (max a 1 - 1) := by
  have h1 : t ^ (a - 1) ≤ t ^ (max a 1 - 1) :=
    Real.rpow_le_rpow_of_exponent_le ht.le (by linarith [le_max_left a 1])
  have h2 : exp (-(π * t)) ≤ exp (-t) := by
    apply exp_le_exp.mpr
    nlinarith [Real.two_le_pi]
  calc t ^ (a - 1) * exp (-(π * t)) ≤ t ^ (max a 1 - 1) * exp (-t) :=
        mul_le_mul h1 h2 (exp_pos _).le (Real.rpow_nonneg (by linarith) _)
    _ = exp (-t) * t ^ (max a 1 - 1) := mul_comm _ _

theorem integrableOn_rpow_mul_exp (a : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * exp (-(π * t))) (Ioi 1) := by
  have hm : 0 < max a 1 := lt_of_lt_of_le one_pos (le_max_right a 1)
  have hG : IntegrableOn (fun t : ℝ => exp (-t) * t ^ (max a 1 - 1)) (Ioi 1) :=
    (GammaIntegral_convergent hm).mono_set (Ioi_subset_Ioi zero_le_one)
  refine hG.mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.mp ht]) _)
      (exp_pos _).le)]
    exact rpow_mul_exp_le ht

/-- `∫_1^∞ t^{a−1} e^{−πt} dt ≤ Γ(max a 1)`. -/
theorem integral_rpow_mul_exp_le_Gamma (a : ℝ) :
    ∫ t in Ioi 1, t ^ (a - 1) * exp (-(π * t)) ≤ Gamma (max a 1) := by
  have hm : 0 < max a 1 := lt_of_lt_of_le one_pos (le_max_right a 1)
  rw [Gamma_eq_integral hm]
  have hG : IntegrableOn (fun t : ℝ => exp (-t) * t ^ (max a 1 - 1)) (Ioi 1) :=
    (GammaIntegral_convergent hm).mono_set (Ioi_subset_Ioi zero_le_one)
  calc ∫ t in Ioi 1, t ^ (a - 1) * exp (-(π * t))
      ≤ ∫ t in Ioi 1, exp (-t) * t ^ (max a 1 - 1) := by
        apply setIntegral_mono_on (integrableOn_rpow_mul_exp a) hG measurableSet_Ioi
        intro t ht
        exact rpow_mul_exp_le ht
    _ ≤ ∫ t in Ioi 0, exp (-t) * t ^ (max a 1 - 1) := by
        apply setIntegral_mono_set (GammaIntegral_convergent hm)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)
        · exact (Ioi_subset_Ioi zero_le_one).eventuallyLE

/-- The archimedean growth envelope `G a = exp (2 (|a|+2)^{3/2})`. -/
noncomputable def G (a : ℝ) : ℝ := exp (2 * (|a| + 2) ^ (3 / 2 : ℝ))

theorem G_pos (a : ℝ) : 0 < G a := exp_pos _

theorem Gamma_max_le_G (a : ℝ) : Gamma (max a 1) ≤ G a := by
  refine (Gamma_le_exp (le_max_right a 1)).trans ?_
  unfold G
  apply exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow (by linarith [le_max_right a 1]) _ (by norm_num)
  rcases le_total a 1 with h | h
  · rw [max_eq_right h]
    linarith [abs_nonneg a]
  · rw [max_eq_left h]
    linarith [le_abs_self a]

/-- `∫_1^∞ t^{a−1} e^{−πt} dt ≤ G a`. -/
theorem integral_rpow_mul_exp_le_G (a : ℝ) :
    ∫ t in Ioi 1, t ^ (a - 1) * exp (-(π * t)) ≤ G a :=
  (integral_rpow_mul_exp_le_Gamma a).trans (Gamma_max_le_G a)

end Soma.Holonics.RH.GammaGrowth
