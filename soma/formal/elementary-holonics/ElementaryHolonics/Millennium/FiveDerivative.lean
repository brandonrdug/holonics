import ElementaryHolonics.Millennium.FiveTheta

/-!
# FiveDerivative: the derivative at the center is the odd sector's first moment

**The order-exactly-one deed of the rank-one campaign at five.**  The completed
L-function `Λ₅` is odd under its reflection (`Λ₅(2−s) = −Λ₅(s)`), so its central value
dies by parity; the first surviving information is the derivative, and folding the
Mellin integral at the fixed point of the reflection presents it as a manifestly
one-signed object:

* **`theDerivativeIsTheOddSectorFirstMoment`** —
  `Λ₅′(1) = 2·∫₁^∞ θ₅(t)·log t dt`: the derivative of the completed L-function at the
  center equals twice the logarithmic first moment of the theta function over the
  fundamental half-line.  No Gross–Zagier input: the Mellin transform differentiates
  under the integral, and the `t ↦ 1/t` fold carries the `(0,1)` half onto `(1,∞)`
  through the sign-`−1` functional equation, the two halves agreeing exactly.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FiveDerivative

open Real HurwitzZeta Complex MeasureTheory Set
open Soma.Holonics.Millennium.FiveTheta

/-! ## 1. The theta vanishes on the nonpositive line -/

lemma theta5_nonpos {t : ℝ} (ht : t ≤ 0) : theta5 t = 0 := by
  unfold theta5
  have harg : 20 * Real.sqrt 2 * t ≤ 0 := by
    have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  have hz : ∀ e ∈ Finset.range 5, ∀ d ∈ Finset.range 10,
      (w5 e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * t) *
         evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * t)) = 0 := by
    intro e _ d _
    rw [oddKernel_undef _ harg]
    ring
  rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => hz e he d hd]
  simp

/-! ## 2. The derivative of `Λ₅` at the center, as a Mellin integral -/

private def f5 : ℝ → ℂ := Complex.ofReal ∘ theta5

private def logf5 : ℝ → ℂ := fun t => Real.log t • f5 t

private lemma lambda5_eq_mellin : lambda5 = mellin f5 := by
  funext s
  exact ((theCompletedLFunctionAtFiveHasMellin s).2).symm

private lemma hasDerivAt_lambda5_one :
    MellinConvergent logf5 1 ∧ HasDerivAt (mellin f5) (mellin logf5 1) 1 := by
  have hfc : LocallyIntegrableOn f5 (Ioi 0) := fiveFEPair.hf_int
  have hf_top : f5 =O[Filter.atTop] (· ^ (-(2 : ℝ))) := by
    have h := isBigO_atTop_theta5 (-(2 : ℝ))
    exact isBigO_ofReal_left.mpr h
  have hf_bot : f5 =O[nhdsWithin 0 (Ioi 0)] (· ^ (-(0 : ℝ))) := by
    have h := fiveFEPair.hf_zero' (-(0 : ℝ))
    exact h
  exact mellin_hasDerivAt_of_isBigO_rpow hfc hf_top (by norm_num) hf_bot (by norm_num)

/-- The derivative of the completed L-function at the center is the Mellin transform of
the log-weighted theta at one. -/
lemma deriv_lambda5_one : deriv lambda5 1 = mellin logf5 1 := by
  rw [lambda5_eq_mellin]
  exact hasDerivAt_lambda5_one.2.deriv

/-! ## 3. The fold: the two half-lines agree through the odd reflection -/

private def gPlus : ℝ → ℂ := fun t => if 1 < t then ((Real.log t * theta5 t : ℝ) : ℂ) else 0

private def gMinus : ℝ → ℂ := fun t => if t ≤ 1 then ((Real.log t * theta5 t : ℝ) : ℂ) else 0

private lemma logf5_split (t : ℝ) : logf5 t = gPlus t + gMinus t := by
  unfold logf5 gPlus gMinus f5
  rcases le_or_gt t 1 with h | h
  · rw [if_neg (not_lt.mpr h), if_pos h]
    simp only [Function.comp_apply, Complex.real_smul]
    push_cast
    ring
  · rw [if_pos h, if_neg (not_le.mpr h)]
    simp only [Function.comp_apply, Complex.real_smul]
    push_cast
    ring

/-- The inversion carries the lower half onto `t²` times the upper half — the pointwise
form of the fold, through the sign-`−1` functional equation. -/
private lemma gMinus_inv (t : ℝ) : gMinus t⁻¹ = ((t ^ 2 : ℝ) : ℂ) * gPlus t := by
  unfold gMinus gPlus
  rcases le_or_gt t 0 with ht | ht
  · have hinv : t⁻¹ ≤ 0 := inv_nonpos.mpr ht
    rw [if_pos (hinv.trans (by norm_num)), if_neg (not_lt.mpr (ht.trans (by norm_num)))]
    rw [theta5_nonpos hinv]
    push_cast
    ring
  · rcases lt_trichotomy t 1 with ht1 | ht1 | ht1
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr ht1
      rw [if_neg (not_le.mpr hinv), if_neg (not_lt.mpr ht1.le)]
      ring
    · subst ht1
      rw [inv_one, if_pos le_rfl, if_neg (lt_irrefl 1), Real.log_one]
      push_cast
      ring
    · have hinv : t⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact ht1.le
      rw [if_pos hinv, if_pos ht1]
      have h1 : theta5 t⁻¹ = -(t ^ 2) * theta5 t := by
        rw [show t⁻¹ = 1 / t from (one_div t).symm]
        exact theFiveThetaFunctionalEquation (by linarith)
      rw [h1, Real.log_inv]
      push_cast
      ring

/-- The `t ↦ t²` shift at the Mellin level. -/
private lemma mellin_sq_shift (g : ℝ → ℂ) (s : ℂ) :
    mellin (fun t => ((t ^ 2 : ℝ) : ℂ) * g t) s = mellin g (s + 2) := by
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht'.ne'
  show (t : ℂ) ^ (s - 1) • (((t ^ 2 : ℝ) : ℂ) * g t) = (t : ℂ) ^ (s + 2 - 1) • g t
  rw [smul_eq_mul, smul_eq_mul]
  rw [show ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) ^ (2 : ℂ) from by
    rw [show ((t ^ 2 : ℝ) : ℂ) = ((t : ℂ)) ^ (2 : ℕ) from by push_cast; ring,
      ← cpow_natCast]
    norm_num]
  rw [show (t : ℂ) ^ (s - 1) * ((t : ℂ) ^ (2 : ℂ) * g t)
      = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (2 : ℂ) * g t from by ring,
    ← cpow_add _ _ hne]
  congr 2
  ring

/-- **The fold at the center**: the Mellin transform of the lower half at one equals
that of the upper half. -/
private lemma mellin_gMinus_eq_gPlus : mellin gMinus 1 = mellin gPlus 1 := by
  have h1 : mellin (fun t => gMinus t⁻¹) (-1) = mellin gMinus (-(-1)) :=
    mellin_comp_inv gMinus (-1)
  rw [show (-(-1) : ℂ) = 1 from by norm_num] at h1
  have h2 : mellin (fun t => gMinus t⁻¹) (-1)
      = mellin (fun t => ((t ^ 2 : ℝ) : ℂ) * gPlus t) (-1) := by
    congr 1
    funext t
    exact gMinus_inv t
  rw [h2, mellin_sq_shift gPlus (-1)] at h1
  rw [show (-1 : ℂ) + 2 = 1 from by norm_num] at h1
  exact h1.symm

/-! ## 4. Integrability of the two halves -/

private lemma aesm_core :
    AEStronglyMeasurable (fun t : ℝ => ((Real.log t * theta5 t : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine Continuous.comp_continuousOn continuous_ofReal ?_
  exact ContinuousOn.mul (Real.continuousOn_log.mono fun t ht => ne_of_gt ht)
    continuousOn_theta5

private lemma gPlus_eq_indicator :
    gPlus = Set.indicator (Ioi 1) (fun t : ℝ => ((Real.log t * theta5 t : ℝ) : ℂ)) := by
  funext t
  rw [Set.indicator_apply]
  unfold gPlus
  rcases lt_or_ge 1 t with h | h
  · rw [if_pos h, if_pos (Set.mem_Ioi.mpr h)]
  · rw [if_neg (not_lt.mpr h), if_neg (by simpa using not_lt.mpr h)]

private lemma aesm_gPlus : AEStronglyMeasurable gPlus (volume.restrict (Ioi 0)) := by
  rw [gPlus_eq_indicator]
  exact aesm_core.indicator measurableSet_Ioi

private lemma aesm_gMinus : AEStronglyMeasurable gMinus (volume.restrict (Ioi 0)) := by
  have h : gMinus = fun t => logf5 t - gPlus t := by
    funext t
    have := logf5_split t
    linear_combination -this
  rw [h]
  have haesm_logf5 : AEStronglyMeasurable logf5 (volume.restrict (Ioi 0)) := by
    have h2 : ∀ t ∈ Ioi (0 : ℝ), logf5 t = ((Real.log t * theta5 t : ℝ) : ℂ) := by
      intro t _
      unfold logf5 f5
      simp only [Function.comp_apply, Complex.real_smul]
      push_cast
      ring
    exact aesm_core.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (h2 t ht).symm)
  exact haesm_logf5.sub aesm_gPlus

private lemma integrand_eq (g : ℝ → ℂ) :
    (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) - 1) • g t) = g := by
  funext t
  rw [show (1 : ℂ) - 1 = 0 from by norm_num, cpow_zero, one_smul]

private lemma integrableOn_logf5 : IntegrableOn logf5 (Ioi 0) := by
  have h := hasDerivAt_lambda5_one.1
  unfold MellinConvergent at h
  rwa [integrand_eq logf5] at h

private lemma norm_gPlus_le (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : ‖gPlus t‖ ≤ ‖logf5 t‖ := by
  unfold gPlus logf5 f5
  simp only [Function.comp_apply, Complex.real_smul]
  split_ifs
  · apply le_of_eq
    congr 1
    push_cast
    ring
  · simp only [norm_zero]
    positivity

private lemma norm_gMinus_le (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : ‖gMinus t‖ ≤ ‖logf5 t‖ := by
  unfold gMinus logf5 f5
  simp only [Function.comp_apply, Complex.real_smul]
  split_ifs
  · apply le_of_eq
    congr 1
    push_cast
    ring
  · simp only [norm_zero]
    positivity

private lemma integrableOn_gPlus : IntegrableOn gPlus (Ioi 0) := by
  refine Integrable.mono integrableOn_logf5 aesm_gPlus ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_gPlus_le t ht

private lemma integrableOn_gMinus : IntegrableOn gMinus (Ioi 0) := by
  refine Integrable.mono integrableOn_logf5 aesm_gMinus ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_gMinus_le t ht

/-! ## 5. The first-moment formula -/

/-- **The derivative at the center is the odd sector's first moment**:
`Λ₅′(1) = 2·∫₁^∞ θ₅(t)·log t dt`.  The route past the Gross–Zagier landmark at this
instance: the sign-`−1` reflection kills the value and presents the derivative as a
single fundamental-domain integral. -/
theorem theDerivativeIsTheOddSectorFirstMoment :
    deriv lambda5 1 = 2 * ∫ t in Ioi (1 : ℝ), ((Real.log t * theta5 t : ℝ) : ℂ) := by
  rw [deriv_lambda5_one]
  have hsplit : mellin logf5 1 = mellin gPlus 1 + mellin gMinus 1 := by
    unfold mellin
    rw [integrand_eq logf5, integrand_eq gPlus, integrand_eq gMinus]
    rw [show logf5 = fun t => gPlus t + gMinus t from funext logf5_split]
    exact integral_add integrableOn_gPlus integrableOn_gMinus
  rw [hsplit, mellin_gMinus_eq_gPlus]
  have hval : mellin gPlus 1 = ∫ t in Ioi (1 : ℝ), ((Real.log t * theta5 t : ℝ) : ℂ) := by
    unfold mellin
    rw [integrand_eq gPlus, gPlus_eq_indicator]
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 :=
      Set.inter_eq_left.mpr fun t ht => Set.mem_Ioi.mpr (lt_trans one_pos (Set.mem_Ioi.mp ht))
    rw [hset]
  rw [hval]
  ring

end Soma.Holonics.Millennium.FiveDerivative
