import ElementaryHolonics.Millennium.FiveDerivative
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# FivePositivity: the odd sector's first moment is strictly positive

**The closing analytic deed of the rank-one campaign at five.**  The derivative of the
completed L-function at the center is `2·∫₁^∞ θ₅(t)·log t dt`
(`theDerivativeIsTheOddSectorFirstMoment`), and this file proves the integral strictly
positive by certified exact arithmetic: the lattice class sum integrates term by term,
the founding class `(k,l) = (0,0)` contributes `∫₁^∞ e^{−αt}·log t dt ≥ e^{−3α}/α`,
and the entire remaining population is dominated through the Gaussian product bound
with every exponential enclosed by rational `(1 + x/64)^{64}` certificates.  Margin
`≈ 0.47` against the tail bound `≈ 1.83`; no floating point anywhere.

* **`theOddMomentIsPositive`** — `0 < ∫₁^∞ θ₅(t)·log t dt`;
* **`theDerivativeDoesNotVanishAtFive`** — `Λ₅′(1) ≠ 0`: with the kernel-checked
  `Λ₅(1) = 0`, the analytic order at the center is exactly one.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FivePositivity

open Real HurwitzZeta Complex MeasureTheory Set
open Soma.Holonics.Millennium.FiveTheta Soma.Holonics.Millennium.FiveDerivative

/-! ## 1. The decay rate and its rational enclosure -/

/-- The decay rate of the theta at five: `α = π√2/20`, conductor `800`. -/
def al : ℝ := π * Real.sqrt 2 / 20

lemma sqrt2_lo : (1414213 : ℝ) / 1000000 < Real.sqrt 2 := by
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

lemma sqrt2_hi : Real.sqrt 2 < (1414214 : ℝ) / 1000000 := by
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

lemma al_lo : (2221 : ℝ) / 10000 < al := by
  unfold al
  nlinarith [Real.pi_gt_d6, sqrt2_lo, Real.sqrt_nonneg 2, Real.pi_pos]

lemma al_hi : al < (2222 : ℝ) / 10000 := by
  unfold al
  nlinarith [Real.pi_lt_d6, sqrt2_hi, Real.sqrt_nonneg 2, Real.pi_pos]

lemma al_pos : 0 < al := lt_trans (by norm_num) al_lo

/-! ## 2. Exponential enclosures by sixty-fourth powers -/

private lemma exp_ge_pow64 {x : ℝ} (hx : 0 ≤ x) : (1 + x / 64) ^ (64 : ℕ) ≤ rexp x := by
  have h1 : 1 + x / 64 ≤ rexp (x / 64) := by
    have := Real.add_one_le_exp (x / 64)
    linarith
  calc (1 + x / 64) ^ (64 : ℕ) ≤ (rexp (x / 64)) ^ (64 : ℕ) :=
        pow_le_pow_left₀ (by positivity) h1 64
    _ = rexp x := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

private lemma exp_le_pow64 {x : ℝ} (h0 : 0 ≤ x) (h64 : x < 64) :
    rexp x ≤ ((1 - x / 64)⁻¹) ^ (64 : ℕ) := by
  have hpos : 0 < 1 - x / 64 := by
    have : x / 64 < 1 := (div_lt_one (by norm_num : (0:ℝ) < 64)).mpr h64
    linarith
  have h2 : 1 - x / 64 ≤ rexp (-(x / 64)) := by
    have := Real.add_one_le_exp (-(x / 64))
    linarith
  have h4 : (1 - x / 64) * rexp (x / 64) ≤ 1 := by
    calc (1 - x / 64) * rexp (x / 64) ≤ rexp (-(x / 64)) * rexp (x / 64) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have h5 : rexp (x / 64) ≤ (1 - x / 64)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpos]
    linarith [h4]
  calc rexp x = (rexp (x / 64)) ^ (64 : ℕ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ ≤ ((1 - x / 64)⁻¹) ^ (64 : ℕ) := pow_le_pow_left₀ (Real.exp_pos _).le h5 64

private lemma exp_lower_of_le {c q : ℝ} (hc : 0 ≤ c) (h : q ≤ (1 + c / 64) ^ (64 : ℕ)) :
    q ≤ rexp c := h.trans (exp_ge_pow64 hc)

private lemma exp_upper_of_le {c q : ℝ} (h0 : 0 ≤ c) (h64 : c < 64)
    (h : ((1 - c / 64)⁻¹) ^ (64 : ℕ) ≤ q) : rexp c ≤ q := (exp_le_pow64 h0 h64).trans h

/-- Convert a lower bound on `e^c` into an upper bound on `e^{−c}`. -/
private lemma expneg_upper {c q : ℝ} (hq : 0 < q) (h : q⁻¹ ≤ rexp c) : rexp (-c) ≤ q := by
  rw [Real.exp_neg]
  have he : (0 : ℝ) < rexp c := Real.exp_pos _
  rw [inv_le_comm₀ he hq]
  exact h

/-- Convert an upper bound on `e^c` into a lower bound on `e^{−c}`. -/
private lemma expneg_lower {c q : ℝ} (hq : 0 < q) (h : rexp c ≤ q⁻¹) : q ≤ rexp (-c) := by
  rw [Real.exp_neg]
  have he : (0 : ℝ) < rexp c := Real.exp_pos _
  rw [le_inv_comm₀ hq he]
  exact h

/-! ## 3. The eight certified exponential bounds -/

set_option maxHeartbeats 4000000 in
/-- `e^{−8α} ≤ 0.1734`. -/
private lemma bd_r : rexp (-(8 * al)) ≤ (1734 : ℝ) / 10000 := by
  refine expneg_upper (by norm_num) ?_
  have h1 : ((17768 : ℝ) / 10000) ≤ 8 * al := by nlinarith [al_lo]
  refine le_trans (exp_lower_of_le (show (0:ℝ) ≤ (17768 : ℝ)/10000 by norm_num) ?_)
    (Real.exp_le_exp.mpr h1)
  norm_num

set_option maxHeartbeats 4000000 in
/-- `e^{−16α} ≤ 0.0315`. -/
private lemma bd_q : rexp (-(16 * al)) ≤ (315 : ℝ) / 10000 := by
  refine expneg_upper (by norm_num) ?_
  have h1 : ((35536 : ℝ) / 10000) ≤ 16 * al := by nlinarith [al_lo]
  refine le_trans (exp_lower_of_le (show (0:ℝ) ≤ (35536 : ℝ)/10000 by norm_num) ?_)
    (Real.exp_le_exp.mpr h1)
  norm_num

set_option maxHeartbeats 4000000 in
/-- `e^{7α} ≤ 4.84`. -/
private lemma bd_e7 : rexp (7 * al) ≤ (4840 : ℝ) / 1000 := by
  have h1 : 7 * al ≤ (15554 : ℝ) / 10000 := by nlinarith [al_hi]
  refine le_trans (Real.exp_le_exp.mpr h1) ?_
  refine exp_upper_of_le (by norm_num) (by norm_num) ?_
  norm_num

set_option maxHeartbeats 4000000 in
/-- `e^{4α} ≤ 2.45`. -/
private lemma bd_e4 : rexp (4 * al) ≤ (2450 : ℝ) / 1000 := by
  have h1 : 4 * al ≤ (8888 : ℝ) / 10000 := by nlinarith [al_hi]
  refine le_trans (Real.exp_le_exp.mpr h1) ?_
  refine exp_upper_of_le (by norm_num) (by norm_num) ?_
  norm_num

set_option maxHeartbeats 4000000 in
/-- `e^{−α} ≤ 0.8012`. -/
private lemma bd_M1 : rexp (-al) ≤ (8012 : ℝ) / 10000 := by
  have h : rexp (-(1 * al)) ≤ (8012 : ℝ) / 10000 := by
    refine expneg_upper (by norm_num) ?_
    have h1 : ((2221 : ℝ) / 10000) ≤ 1 * al := by nlinarith [al_lo]
    refine le_trans (exp_lower_of_le (show (0:ℝ) ≤ (2221 : ℝ)/10000 by norm_num) ?_)
      (Real.exp_le_exp.mpr h1)
    norm_num
  simpa using h

set_option maxHeartbeats 4000000 in
/-- `0.8004 ≤ e^{−α}`. -/
private lemma bd_m1 : (8004 : ℝ) / 10000 ≤ rexp (-al) := by
  have h : (8004 : ℝ) / 10000 ≤ rexp (-(1 * al)) := by
    refine expneg_lower (by norm_num) ?_
    have h1 : 1 * al ≤ (2222 : ℝ) / 10000 := by nlinarith [al_hi]
    refine le_trans (Real.exp_le_exp.mpr h1) ?_
    refine exp_upper_of_le (by norm_num) (by norm_num) ?_
    norm_num
  simpa using h

set_option maxHeartbeats 4000000 in
/-- `0.3255 ≤ e^{−5α}`. -/
private lemma bd_m5 : (3255 : ℝ) / 10000 ≤ rexp (-(5 * al)) := by
  refine expneg_lower (by norm_num) ?_
  have h1 : 5 * al ≤ (11110 : ℝ) / 10000 := by nlinarith [al_hi]
  refine le_trans (Real.exp_le_exp.mpr h1) ?_
  refine exp_upper_of_le (by norm_num) (by norm_num) ?_
  norm_num

set_option maxHeartbeats 4000000 in
/-- `0.5109 ≤ e^{−3α}`. -/
private lemma bd_m3 : (5109 : ℝ) / 10000 ≤ rexp (-(3 * al)) := by
  refine expneg_lower (by norm_num) ?_
  have h1 : 3 * al ≤ (6666 : ℝ) / 10000 := by nlinarith [al_hi]
  refine le_trans (Real.exp_le_exp.mpr h1) ?_
  refine exp_upper_of_le (by norm_num) (by norm_num) ?_
  norm_num

/-! ## 4. The four integral laws on the half-line -/

private lemma integrableOn_expNeg {a β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ => rexp (-β * t)) (Ioi a) :=
  exp_neg_integrableOn_Ioi a hβ

private lemma tendsto_expNeg {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto (fun t : ℝ => rexp (-β * t)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => β * t) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hβ
  have h2 : Filter.Tendsto (fun t : ℝ => -(β * t)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h1
  have h3 := Real.tendsto_exp_atBot.comp h2
  refine h3.congr fun t => ?_
  simp only [Function.comp_apply]
  congr 1
  ring

/-- `∫_a^∞ e^{−βt} dt = e^{−βa}/β`. -/
private lemma integral_expNeg (a : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∫ t in Ioi a, rexp (-β * t) = rexp (-β * a) / β := by
  have hd : ∀ x ∈ Ici a, HasDerivAt (fun t : ℝ => -rexp (-β * t) / β)
      (rexp (-β * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -β * t) (-β) x := by
      simpa using (hasDerivAt_id x).const_mul (-β)
    have h2 : HasDerivAt (fun t : ℝ => rexp (-β * t)) (rexp (-β * x) * -β) x :=
      (Real.hasDerivAt_exp (-β * x)).comp x h1
    have h3 : HasDerivAt (fun t : ℝ => -rexp (-β * t) / β)
        (-(rexp (-β * x) * -β) / β) x := (h2.neg).div_const β
    convert h3 using 1
    field_simp
  have htend : Filter.Tendsto (fun t : ℝ => -rexp (-β * t) / β) Filter.atTop (nhds 0) := by
    have h := ((tendsto_expNeg hβ).neg).div_const β
    simp only [neg_zero, zero_div] at h
    refine h.congr fun t => ?_
    rw [neg_div]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_expNeg hβ) htend
  rw [h]
  field_simp
  ring

/-- The linear-weight bound `t·e^{−βt} ≤ (2/β)·e^{−(β/2)t}`. -/
private lemma linear_exp_bound {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    t * rexp (-β * t) ≤ (2 / β) * rexp (-(β / 2) * t) := by
  have h1 : β / 2 * t ≤ rexp (β / 2 * t) := by
    have := Real.add_one_le_exp (β / 2 * t)
    linarith
  have h2 : rexp (-β * t) = rexp (-(β / 2) * t) * rexp (-(β / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : t * rexp (-(β / 2) * t) ≤ 2 / β := by
    have h4 : rexp (-(β / 2) * t) = (rexp (β / 2 * t))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    have h5 : t * (rexp (β / 2 * t))⁻¹ ≤ 2 / β := by
      rw [mul_inv_le_iff₀ (Real.exp_pos _)]
      calc t = (2 / β) * (β / 2 * t) := by field_simp
        _ ≤ (2 / β) * rexp (β / 2 * t) := by
            apply mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 / β * rexp (β / 2 * t) := by ring
    rw [h4]
    exact h5
  calc t * rexp (-β * t) = (t * rexp (-(β / 2) * t)) * rexp (-(β / 2) * t) := by
        rw [h2]; ring
    _ ≤ (2 / β) * rexp (-(β / 2) * t) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

private lemma integrableOn_linear_expNeg {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ => t * rexp (-β * t)) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_expNeg (a := 1) (show 0 < β/2 by positivity)).const_mul
    (2 / β)) ?_ ?_
  · exact (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul
      continuous_id))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (0 : ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact linear_exp_bound hβ ht1

/-- `∫_1^∞ t·e^{−βt} dt = (β+1)·e^{−β}/β²`. -/
private lemma integral_linear_expNeg {β : ℝ} (hβ : 0 < β) :
    ∫ t in Ioi 1, t * rexp (-β * t) = (β + 1) * rexp (-β) / β ^ 2 := by
  have hd : ∀ x ∈ Ici (1 : ℝ), HasDerivAt
      (fun t : ℝ => -((t / β + 1 / β ^ 2) * rexp (-β * t)))
      (x * rexp (-β * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -β * t) (-β) x := by
      simpa using (hasDerivAt_id x).const_mul (-β)
    have h2 : HasDerivAt (fun t : ℝ => rexp (-β * t)) (rexp (-β * x) * -β) x :=
      (Real.hasDerivAt_exp (-β * x)).comp x h1
    have h3 : HasDerivAt (fun t : ℝ => t / β + 1 / β ^ 2) (1 / β) x := by
      simpa using ((hasDerivAt_id x).div_const β).add_const (1 / β ^ 2)
    have h4 := (h3.mul h2).neg
    convert h4 using 1
    field_simp
    ring
  have htend : Filter.Tendsto (fun t : ℝ => -((t / β + 1 / β ^ 2) * rexp (-β * t)))
      Filter.atTop (nhds 0) := by
    have hA : Filter.Tendsto (fun t : ℝ => t / β * rexp (-β * t)) Filter.atTop (nhds 0) := by
      have hcomp : Filter.Tendsto (fun t : ℝ => β * t) Filter.atTop Filter.atTop :=
        Filter.tendsto_id.const_mul_atTop hβ
      have hbase : Filter.Tendsto (fun y : ℝ => y * rexp (-y)) Filter.atTop (nhds 0) := by
        simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have := (hbase.comp hcomp).div_const (β ^ 2)
      simp only [Function.comp] at this
      rw [show (0 : ℝ) / β ^ 2 = 0 from by ring] at this
      refine this.congr fun t => ?_
      rw [show -(β * t) = -β * t from by ring]
      field_simp
    have hB : Filter.Tendsto (fun t : ℝ => 1 / β ^ 2 * rexp (-β * t))
        Filter.atTop (nhds 0) := by
      have := (tendsto_expNeg hβ).const_mul (1 / β ^ 2)
      simpa using this
    have h6 := (hA.add hB).neg
    simp only [add_zero, neg_zero] at h6
    refine h6.congr fun t => ?_
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_linear_expNeg hβ) htend
  rw [h]
  field_simp
  ring

private lemma integrableOn_log_expNeg {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ => Real.log t * rexp (-β * t)) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_linear_expNeg hβ) ?_ ?_
  · exact ((Real.measurable_log.mul (Real.measurable_exp.comp
      (measurable_const.mul measurable_id))).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.log t ≤ t := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- **The upper `J`-bound**: `∫_1^∞ log t·e^{−βt} dt ≤ e^{−β}/β²`. -/
private lemma J_le {β : ℝ} (hβ : 0 < β) :
    ∫ t in Ioi 1, Real.log t * rexp (-β * t) ≤ rexp (-β) / β ^ 2 := by
  have hmono : ∫ t in Ioi 1, Real.log t * rexp (-β * t)
      ≤ ∫ t in Ioi 1, (t - 1) * rexp (-β * t) := by
    refine setIntegral_mono_on (integrableOn_log_expNeg hβ) ?_ measurableSet_Ioi ?_
    · refine ((integrableOn_linear_expNeg hβ).sub (integrableOn_expNeg hβ)).congr ?_
      filter_upwards with t
      simp only [Pi.sub_apply]
      ring
    · intro t ht
      have ht1 : (1 : ℝ) < t := ht
      exact mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (by linarith))
        (Real.exp_pos _).le
  have hval : ∫ t in Ioi 1, (t - 1) * rexp (-β * t) = rexp (-β) / β ^ 2 := by
    have hsplit : ∫ t in Ioi 1, (t - 1) * rexp (-β * t)
        = (∫ t in Ioi 1, t * rexp (-β * t)) - ∫ t in Ioi 1, rexp (-β * t) := by
      rw [← integral_sub (integrableOn_linear_expNeg hβ) (integrableOn_expNeg hβ)]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    rw [hsplit, integral_linear_expNeg hβ, integral_expNeg 1 hβ]
    field_simp
    ring
  rw [← hval]
  exact hmono

private lemma log_expNeg_nonneg {β t : ℝ} (ht : 1 < t) :
    0 ≤ Real.log t * rexp (-β * t) :=
  mul_nonneg (Real.log_nonneg ht.le) (Real.exp_pos _).le

/-- **The lower `J`-bound at the founding class**: `e^{−3α}/α ≤ ∫_1^∞ log t·e^{−αt} dt`. -/
private lemma J_lo : rexp (-(3 * al)) / al ≤ ∫ t in Ioi 1, Real.log t * rexp (-al * t) := by
  have hα := al_pos
  have h3sub : ∫ t in Ioi 3, Real.log t * rexp (-al * t)
      ≤ ∫ t in Ioi 1, Real.log t * rexp (-al * t) := by
    refine setIntegral_mono_set (integrableOn_log_expNeg hα) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact log_expNeg_nonneg ht
    · exact HasSubset.Subset.eventuallyLE fun t ht =>
        lt_trans (by norm_num) (Set.mem_Ioi.mp ht)
  have hone : ∫ t in Ioi 3, rexp (-al * t) ≤ ∫ t in Ioi 3, Real.log t * rexp (-al * t) := by
    refine setIntegral_mono_on (integrableOn_expNeg hα)
      ((integrableOn_log_expNeg hα).mono_set fun t ht =>
        lt_trans (by norm_num) (Set.mem_Ioi.mp ht)) measurableSet_Ioi ?_
    intro t ht
    have ht3 : (3 : ℝ) < t := ht
    have hlog1 : 1 ≤ Real.log t := by
      have h1 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    calc rexp (-al * t) = 1 * rexp (-al * t) := by ring
      _ ≤ Real.log t * rexp (-al * t) :=
          mul_le_mul_of_nonneg_right hlog1 (Real.exp_pos _).le
  have hval : ∫ t in Ioi 3, rexp (-al * t) = rexp (-al * 3) / al := integral_expNeg 3 hα
  have hcast : rexp (-(3 * al)) / al = rexp (-al * 3) / al := by
    congr 2
    ring
  rw [hcast, ← hval]
  exact le_trans hone h3sub

/-! ## 5. The lattice series and its weights -/

/-- The class norm. -/
private def NN (p : ℤ × ℤ) : ℤ := (4 * p.1 + 1) ^ 2 + 4 * p.2 ^ 2

/-- The class weight. -/
private def wI (p : ℤ × ℤ) : ℝ :=
  ((4 * p.1 + 1 : ℤ) : ℝ) * (if p.2 % 2 = 0 then (1 : ℝ) else -1) * (chi5 (NN p) : ℝ)

/-- One lattice term of the theta. -/
private def latTerm (t : ℝ) (p : ℤ × ℤ) : ℝ := wI p * rexp (-al * ((NN p : ℤ) : ℝ) * t)

private lemma hasSum_latTerm {t : ℝ} (ht : 0 < t) : HasSum (latTerm t) (theta5 t) := by
  refine (theFiveThetaIsItsLatticeSum ht).congr_fun fun p => ?_
  unfold latTerm wI NN al
  ring

private lemma NN_ge_one (p : ℤ × ℤ) : 1 ≤ NN p := by
  unfold NN
  have h1 : (4 * p.1 + 1 : ℤ) ≠ 0 := by omega
  nlinarith [Int.one_le_abs h1, sq_abs (4 * p.1 + 1), sq_nonneg p.2, sq_nonneg (4 * p.1 + 1),
    abs_nonneg (4 * p.1 + 1)]

private lemma NN_pos_real (p : ℤ × ℤ) : (0 : ℝ) < ((NN p : ℤ) : ℝ) := by
  have := NN_ge_one p
  exact_mod_cast lt_of_lt_of_le zero_lt_one this

private lemma chi5_five : chi5 5 = 0 := by decide

private lemma NN_ge_nine {p : ℤ × ℤ} (hp : p ≠ ((0 : ℤ), (0 : ℤ)))
    (hchi : chi5 (NN p) ≠ 0) : 9 ≤ NN p := by
  obtain ⟨k, l⟩ := p
  unfold NN at hchi ⊢
  by_cases hk : k = 0
  · subst hk
    have hl : l = 0 ∨ l = 1 ∨ l = -1 ∨ 2 ≤ l ∨ l ≤ -2 := by omega
    rcases hl with h | h | h | h | h
    · subst h
      exact absurd rfl hp
    · subst h
      rw [show (4 * (0:ℤ) + 1) ^ 2 + 4 * (1:ℤ) ^ 2 = 5 from by ring] at hchi
      exact absurd chi5_five hchi
    · subst h
      rw [show (4 * (0:ℤ) + 1) ^ 2 + 4 * (-1:ℤ) ^ 2 = 5 from by ring] at hchi
      exact absurd chi5_five hchi
    · nlinarith
    · nlinarith
  · have hk2 : 1 ≤ k ∨ k ≤ -1 := by omega
    rcases hk2 with h | h
    · nlinarith [sq_nonneg l]
    · nlinarith [sq_nonneg l]

private lemma abs_wI_le (p : ℤ × ℤ) : |wI p| ≤ ((NN p : ℤ) : ℝ) := by
  unfold wI
  have h1 : |((4 * p.1 + 1 : ℤ) : ℝ)| ≤ ((NN p : ℤ) : ℝ) := by
    have h2 : |(4 * p.1 + 1 : ℤ)| ≤ NN p := by
      unfold NN
      nlinarith [Int.one_le_abs (show (4 * p.1 + 1 : ℤ) ≠ 0 by omega),
        sq_abs (4 * p.1 + 1), sq_nonneg p.2, abs_nonneg (4 * p.1 + 1)]
    calc |((4 * p.1 + 1 : ℤ) : ℝ)| = ((|4 * p.1 + 1| : ℤ) : ℝ) := by
          rw [Int.cast_abs]
      _ ≤ ((NN p : ℤ) : ℝ) := by exact_mod_cast h2
  have hs : |(if p.2 % 2 = 0 then (1 : ℝ) else -1)| ≤ 1 := by
    split_ifs <;> norm_num
  have hc : |(chi5 (NN p) : ℝ)| ≤ 1 := by
    have := chi5_abs_le (NN p)
    exact_mod_cast this
  calc |((4 * p.1 + 1 : ℤ) : ℝ) * (if p.2 % 2 = 0 then (1 : ℝ) else -1) * (chi5 (NN p) : ℝ)|
      = |((4 * p.1 + 1 : ℤ) : ℝ)| * |(if p.2 % 2 = 0 then (1 : ℝ) else -1)| *
        |(chi5 (NN p) : ℝ)| := by rw [abs_mul, abs_mul]
    _ ≤ ((NN p : ℤ) : ℝ) * 1 * 1 := by
        have h5 : (0 : ℝ) ≤ ((NN p : ℤ) : ℝ) := (NN_pos_real p).le
        refine mul_le_mul (mul_le_mul h1 hs (abs_nonneg _) h5) hc (abs_nonneg _) ?_
        nlinarith
    _ = ((NN p : ℤ) : ℝ) := by ring

/-! ## 6. The Gaussian majorant over the lattice -/

/-- The lattice Gaussian. -/
private def gauss (p : ℤ × ℤ) : ℝ := rexp (-al * ((NN p : ℤ) : ℝ))

private lemma gauss_pos (p : ℤ × ℤ) : 0 < gauss p := Real.exp_pos _

private lemma gauss_factor (p : ℤ × ℤ) :
    gauss p = rexp (-al * (((4 * p.1 + 1) ^ 2 : ℤ) : ℝ)) *
      rexp (-(4 * al) * ((p.2 ^ 2 : ℤ) : ℝ)) := by
  unfold gauss NN
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

private lemma summable_gauss_sq (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℤ => rexp (-c * (n : ℝ) ^ 2) := by
  have hπ := Real.pi_pos
  have h := (HurwitzZeta.hasSum_int_evenKernel 0
    (show (0 : ℝ) < c / π by positivity)).summable
  refine h.congr fun n => ?_
  rw [add_zero]
  congr 1
  field_simp

private lemma summable_gaussA :
    Summable fun k : ℤ => rexp (-al * (((4 * k + 1) ^ 2 : ℤ) : ℝ)) := by
  have hα := al_pos
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => ?_) (summable_gauss_sq al hα)
  rw [Real.exp_le_exp]
  have hk : (k : ℝ) ^ 2 ≤ (((4 * k + 1) ^ 2 : ℤ) : ℝ) := by
    have h : (k ^ 2 : ℤ) ≤ (4 * k + 1) ^ 2 := by nlinarith [sq_nonneg (2 * k), sq_nonneg (2*k+1)]
    exact_mod_cast h
  nlinarith

private lemma summable_gaussB :
    Summable fun l : ℤ => rexp (-(4 * al) * ((l ^ 2 : ℤ) : ℝ)) := by
  have hα := al_pos
  refine (summable_gauss_sq (4 * al) (by positivity)).congr fun n => ?_
  congr 1
  push_cast
  ring

private lemma summable_gauss_lattice : Summable gauss := by
  have h := (summable_gaussA.mul_of_nonneg summable_gaussB
    (fun k => (Real.exp_pos _).le) (fun l => (Real.exp_pos _).le))
  refine h.congr fun p => ?_
  exact (gauss_factor p).symm

/-- The geometric bound for a one-dimensional family dominated away from zero. -/
private lemma tsum_int_le_geometric {f : ℤ → ℝ} {c₀ C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 ≤ C) (hf : Summable f) (h0 : f 0 ≤ c₀)
    (hpos : ∀ k, 0 ≤ f k) (hb : ∀ k : ℤ, k ≠ 0 → f k ≤ C * q ^ k.natAbs) :
    ∑' k : ℤ, f k ≤ c₀ + 2 * C * (q / (1 - q)) := by
  have h1q : 0 < 1 - q := by linarith
  -- the two geometric halves
  have hgeo : Summable fun n : ℕ => C * q ^ (n + 1) := by
    have := (summable_geometric_of_lt_one hq0 hq1).mul_left (C * q)
    refine this.congr fun n => ?_
    rw [pow_succ]
    ring
  have hgeo_val : ∑' n : ℕ, C * q ^ (n + 1) = C * (q / (1 - q)) := by
    have h := tsum_geometric_of_lt_one hq0 hq1
    calc ∑' n : ℕ, C * q ^ (n + 1) = ∑' n : ℕ, (C * q) * q ^ n := by
          refine tsum_congr fun n => ?_
          rw [pow_succ]
          ring
      _ = (C * q) * ∑' n : ℕ, q ^ n := tsum_mul_left
      _ = (C * q) * (1 - q)⁻¹ := by rw [h]
      _ = C * (q / (1 - q)) := by field_simp
  -- majorant with the zero class extracted
  have hsplit : ∑' k : ℤ, f k = f 0 + ∑' k : ℤ, if k = 0 then 0 else f k :=
    hf.tsum_eq_add_tsum_ite 0
  have hposEmb : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := fun a b h => by
    simpa using h
  have hnegEmb : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := fun a b h => by
    simpa using h
  have hite_le : ∑' k : ℤ, (if k = 0 then 0 else f k) ≤ 2 * C * (q / (1 - q)) := by
    have hmaj : ∀ k : ℤ, (if k = 0 then 0 else f k)
        ≤ (if 0 < k then C * q ^ k.natAbs else 0) +
          (if k < 0 then C * q ^ k.natAbs else 0) := by
      intro k
      rcases lt_trichotomy k 0 with h | h | h
      · rw [if_neg (by omega), if_neg (by omega), if_pos h, zero_add]
        exact hb k (by omega)
      · rw [if_pos h, if_neg (by omega), if_neg (by omega)]
        norm_num
      · rw [if_neg (by omega), if_pos h, if_neg (by omega), add_zero]
        exact hb k (by omega)
    have hsummable_pos : Summable fun k : ℤ => if 0 < k then C * q ^ k.natAbs else 0 := by
      refine (Summable.of_norm_bounded (g := fun k : ℤ => C * q ^ k.natAbs) ?_ ?_)
      · -- summable |k|-geometric over ℤ from the two ℕ-halves is subsumed below
        exact Summable.of_nat_of_neg
          ((summable_geometric_of_lt_one hq0 hq1).mul_left C |>.congr fun n => by
            simp [Int.natAbs_natCast])
          (((summable_geometric_of_lt_one hq0 hq1).mul_left C).congr fun n => by
            simp [Int.natAbs_neg, Int.natAbs_natCast])
      · intro k
        rw [Real.norm_eq_abs]
        split_ifs
        · rw [abs_of_nonneg (by positivity)]
        · rw [abs_zero]
          positivity
    have hsummable_neg : Summable fun k : ℤ => if k < 0 then C * q ^ k.natAbs else 0 := by
      refine (Summable.of_norm_bounded (g := fun k : ℤ => C * q ^ k.natAbs) ?_ ?_)
      · exact Summable.of_nat_of_neg
          ((summable_geometric_of_lt_one hq0 hq1).mul_left C |>.congr fun n => by
            simp [Int.natAbs_natCast])
          (((summable_geometric_of_lt_one hq0 hq1).mul_left C).congr fun n => by
            simp [Int.natAbs_neg, Int.natAbs_natCast])
      · intro k
        rw [Real.norm_eq_abs]
        split_ifs
        · rw [abs_of_nonneg (by positivity)]
        · rw [abs_zero]
          positivity
    have hsupp_pos : Function.support (fun k : ℤ => if 0 < k then C * q ^ k.natAbs else 0)
        ⊆ Set.range (fun n : ℕ => (n : ℤ) + 1) := by
      rw [Function.support_subset_iff]
      intro k hk
      have h : 0 < k := by
        by_contra h
        exact hk (if_neg h)
      refine ⟨(k - 1).toNat, ?_⟩
      show (((k - 1).toNat : ℤ)) + 1 = k
      omega
    have hsupp_neg : Function.support (fun k : ℤ => if k < 0 then C * q ^ k.natAbs else 0)
        ⊆ Set.range (fun n : ℕ => -((n : ℤ) + 1)) := by
      rw [Function.support_subset_iff]
      intro k hk
      have h : k < 0 := by
        by_contra h
        exact hk (if_neg h)
      refine ⟨(-k - 1).toNat, ?_⟩
      show -(((-k - 1).toNat : ℤ) + 1) = k
      omega
    have hsum_pos : ∑' k : ℤ, (if 0 < k then C * q ^ k.natAbs else 0)
        ≤ C * (q / (1 - q)) := by
      have hEq : ∑' k : ℤ, (if 0 < k then C * q ^ k.natAbs else 0)
          = ∑' n : ℕ, C * q ^ (n + 1) := by
        rw [← Function.Injective.tsum_eq hposEmb hsupp_pos]
        refine tsum_congr fun n => ?_
        show (if 0 < (n : ℤ) + 1 then C * q ^ ((n : ℤ) + 1).natAbs else 0) = C * q ^ (n + 1)
        rw [if_pos (by omega), show ((n : ℤ) + 1).natAbs = n + 1 from by omega]
      rw [hEq, hgeo_val]
    have hsum_neg : ∑' k : ℤ, (if k < 0 then C * q ^ k.natAbs else 0)
        ≤ C * (q / (1 - q)) := by
      have hEq : ∑' k : ℤ, (if k < 0 then C * q ^ k.natAbs else 0)
          = ∑' n : ℕ, C * q ^ (n + 1) := by
        rw [← Function.Injective.tsum_eq hnegEmb hsupp_neg]
        refine tsum_congr fun n => ?_
        show (if -((n : ℤ) + 1) < 0 then C * q ^ (-((n : ℤ) + 1)).natAbs else 0)
          = C * q ^ (n + 1)
        rw [if_pos (by omega), show (-((n : ℤ) + 1)).natAbs = n + 1 from by omega]
      rw [hEq, hgeo_val]
    have hsum_ite : Summable fun k : ℤ => if k = 0 then 0 else f k := by
      refine Summable.of_norm_bounded (g := f) hf fun k => ?_
      rw [Real.norm_eq_abs]
      split_ifs
      · rw [abs_zero]
        exact hpos k
      · rw [abs_of_nonneg (hpos k)]
    calc ∑' k : ℤ, (if k = 0 then 0 else f k)
        ≤ ∑' k : ℤ, ((if 0 < k then C * q ^ k.natAbs else 0) +
            (if k < 0 then C * q ^ k.natAbs else 0)) :=
          hsum_ite.tsum_le_tsum hmaj (hsummable_pos.add hsummable_neg)
      _ = (∑' k : ℤ, (if 0 < k then C * q ^ k.natAbs else 0)) +
            ∑' k : ℤ, (if k < 0 then C * q ^ k.natAbs else 0) :=
          hsummable_pos.tsum_add hsummable_neg
      _ ≤ C * (q / (1 - q)) + C * (q / (1 - q)) := add_le_add hsum_pos hsum_neg
      _ = 2 * C * (q / (1 - q)) := by ring
  calc ∑' k : ℤ, f k = f 0 + ∑' k : ℤ, (if k = 0 then 0 else f k) := hsplit
    _ ≤ c₀ + 2 * C * (q / (1 - q)) := add_le_add h0 hite_le

/-! ## 7. The two one-dimensional Gaussian bounds -/

private lemma boundA : ∑' k : ℤ, rexp (-al * (((4 * k + 1) ^ 2 : ℤ) : ℝ))
    ≤ (8012 : ℝ) / 10000 + 2 * ((4840 : ℝ) / 1000) *
      (((315 : ℝ) / 10000) / (1 - (315 : ℝ) / 10000)) := by
  refine tsum_int_le_geometric (by norm_num) (by norm_num) (by norm_num) summable_gaussA
    ?_ (fun k => (Real.exp_pos _).le) ?_
  · have h : (((4 * (0 : ℤ) + 1) ^ 2 : ℤ) : ℝ) = 1 := by norm_num
    rw [h, mul_one]
    exact bd_M1
  · intro k hk
    have hj : 1 ≤ k.natAbs := by omega
    have hNge : 16 * (k.natAbs : ℤ) - 7 ≤ (4 * k + 1) ^ 2 := by
      rcases (by omega : 1 ≤ k ∨ k ≤ -1) with h | h
      · have : (k.natAbs : ℤ) = k := by omega
        rw [this]
        nlinarith
      · have : (k.natAbs : ℤ) = -k := by omega
        rw [this]
        nlinarith [sq_nonneg (2 * k + 1), sq_nonneg (k + 1)]
    have hexp : rexp (-al * (((4 * k + 1) ^ 2 : ℤ) : ℝ))
        ≤ rexp (7 * al) * (rexp (-(16 * al))) ^ k.natAbs := by
      rw [show rexp (7 * al) * (rexp (-(16 * al))) ^ k.natAbs
          = rexp (7 * al + (k.natAbs : ℕ) * (-(16 * al))) from by
        rw [Real.exp_add, Real.exp_nat_mul]]
      rw [Real.exp_le_exp]
      have hcast : (16 * (k.natAbs : ℤ) - 7 : ℤ) ≤ ((4 * k + 1) ^ 2 : ℤ) := hNge
      have hcast2 : (16 * (k.natAbs : ℝ) - 7 : ℝ) ≤ (((4 * k + 1) ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast hcast
      nlinarith [al_pos]
    refine hexp.trans ?_
    have h1 := bd_e7
    have h2 : (rexp (-(16 * al))) ^ k.natAbs ≤ ((315 : ℝ) / 10000) ^ k.natAbs :=
      pow_le_pow_left₀ (Real.exp_pos _).le bd_q _
    have h3 : (0 : ℝ) ≤ (rexp (-(16 * al))) ^ k.natAbs := by positivity
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 315/10000 by norm_num) k.natAbs]

private lemma boundB : ∑' l : ℤ, rexp (-(4 * al) * ((l ^ 2 : ℤ) : ℝ))
    ≤ 1 + 2 * ((2450 : ℝ) / 1000) *
      (((1734 : ℝ) / 10000) / (1 - (1734 : ℝ) / 10000)) := by
  refine tsum_int_le_geometric (by norm_num) (by norm_num) (by norm_num) summable_gaussB
    ?_ (fun k => (Real.exp_pos _).le) ?_
  · have h : (((0 : ℤ) ^ 2 : ℤ) : ℝ) = 0 := by norm_num
    rw [h, mul_zero, Real.exp_zero]
  · intro l hl
    have hNge : 8 * (l.natAbs : ℤ) - 4 ≤ 4 * l ^ 2 := by
      rcases (by omega : 1 ≤ l ∨ l ≤ -1) with h | h
      · have : (l.natAbs : ℤ) = l := by omega
        rw [this]
        nlinarith [sq_nonneg (l - 1)]
      · have : (l.natAbs : ℤ) = -l := by omega
        rw [this]
        nlinarith [sq_nonneg (l + 1)]
    have hexp : rexp (-(4 * al) * ((l ^ 2 : ℤ) : ℝ))
        ≤ rexp (4 * al) * (rexp (-(8 * al))) ^ l.natAbs := by
      rw [show rexp (4 * al) * (rexp (-(8 * al))) ^ l.natAbs
          = rexp (4 * al + (l.natAbs : ℕ) * (-(8 * al))) from by
        rw [Real.exp_add, Real.exp_nat_mul]]
      rw [Real.exp_le_exp]
      have hcast2 : (8 * (l.natAbs : ℝ) - 4 : ℝ) ≤ 4 * ((l ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast hNge
      nlinarith [al_pos]
    refine hexp.trans ?_
    have h2 : (rexp (-(8 * al))) ^ l.natAbs ≤ ((1734 : ℝ) / 10000) ^ l.natAbs :=
      pow_le_pow_left₀ (Real.exp_pos _).le bd_r _
    nlinarith [bd_e4, pow_nonneg (show (0:ℝ) ≤ 1734/10000 by norm_num) l.natAbs,
      pow_nonneg (Real.exp_pos (-(8 * al))).le l.natAbs]

/-! ## 8. The lattice Gaussian bound with the three founding classes removed -/

private def excluded (p : ℤ × ℤ) : Prop :=
  p = ((0 : ℤ), (0 : ℤ)) ∨ p = ((0 : ℤ), (1 : ℤ)) ∨ p = ((0 : ℤ), (-1 : ℤ))

private instance : DecidablePred excluded := fun p => by
  unfold excluded
  infer_instance

private lemma tsum_gauss_eq :
    ∑' p : ℤ × ℤ, gauss p
      = (∑' k : ℤ, rexp (-al * (((4 * k + 1) ^ 2 : ℤ) : ℝ))) *
        ∑' l : ℤ, rexp (-(4 * al) * ((l ^ 2 : ℤ) : ℝ)) := by
  have hprod : Summable fun p : ℤ × ℤ =>
      rexp (-al * (((4 * p.1 + 1) ^ 2 : ℤ) : ℝ)) *
        rexp (-(4 * al) * ((p.2 ^ 2 : ℤ) : ℝ)) :=
    summable_gauss_lattice.congr fun p => gauss_factor p
  have h := summable_gaussA.hasSum.mul_eq summable_gaussB.hasSum hprod.hasSum
  calc ∑' p : ℤ × ℤ, gauss p
      = ∑' p : ℤ × ℤ, rexp (-al * (((4 * p.1 + 1) ^ 2 : ℤ) : ℝ)) *
          rexp (-(4 * al) * ((p.2 ^ 2 : ℤ) : ℝ)) := tsum_congr fun p => gauss_factor p
    _ = _ := h.symm

private lemma gauss_value_00 : gauss ((0 : ℤ), (0 : ℤ)) = rexp (-al) := by
  unfold gauss NN
  congr 1
  push_cast
  ring

private lemma gauss_value_01 : gauss ((0 : ℤ), (1 : ℤ)) = rexp (-(5 * al)) := by
  unfold gauss NN
  congr 1
  push_cast
  ring

private lemma gauss_value_0m1 : gauss ((0 : ℤ), (-1 : ℤ)) = rexp (-(5 * al)) := by
  unfold gauss NN
  congr 1
  push_cast
  ring

/-! ## 9. Termwise integration of the lattice series -/

private def IP (p : ℤ × ℤ) : ℝ := ∫ t in Ioi 1, Real.log t * latTerm t p

private lemma beta_pos (p : ℤ × ℤ) : 0 < al * ((NN p : ℤ) : ℝ) :=
  mul_pos al_pos (NN_pos_real p)

private lemma latTerm_form (t : ℝ) (p : ℤ × ℤ) :
    Real.log t * latTerm t p
      = wI p * (Real.log t * rexp (-(al * ((NN p : ℤ) : ℝ)) * t)) := by
  unfold latTerm
  rw [show -(al * ((NN p : ℤ) : ℝ)) * t = -al * ((NN p : ℤ) : ℝ) * t from by ring]
  ring

private lemma integrable_term (p : ℤ × ℤ) :
    IntegrableOn (fun t => Real.log t * latTerm t p) (Ioi 1) := by
  have h := (integrableOn_log_expNeg (beta_pos p)).const_mul (wI p)
  refine h.congr ?_
  filter_upwards with t
  exact (latTerm_form t p).symm

private lemma norm_integral_term (p : ℤ × ℤ) :
    ∫ t in Ioi 1, ‖Real.log t * latTerm t p‖
      = |wI p| * ∫ t in Ioi 1, Real.log t * rexp (-(al * ((NN p : ℤ) : ℝ)) * t) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht1 : (1 : ℝ) < t := ht
  rw [latTerm_form, Real.norm_eq_abs, abs_mul, abs_of_nonneg (log_expNeg_nonneg ht1)]

private lemma norm_integral_le_gen (p : ℤ × ℤ) {c : ℝ} (hc : 0 < c)
    (hcN : c ≤ ((NN p : ℤ) : ℝ)) :
    ∫ t in Ioi 1, ‖Real.log t * latTerm t p‖ ≤ (1 / (c * al ^ 2)) * gauss p := by
  rw [norm_integral_term]
  have hβ := beta_pos p
  have hN0 := NN_pos_real p
  have hw := abs_wI_le p
  have hJ := J_le hβ
  have hJnn : 0 ≤ ∫ t in Ioi 1, Real.log t * rexp (-(al * ((NN p : ℤ) : ℝ)) * t) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => log_expNeg_nonneg ht
  have hα := al_pos
  have hgauss : gauss p = rexp (-(al * ((NN p : ℤ) : ℝ))) := by
    unfold gauss
    congr 1
    ring
  calc |wI p| * ∫ t in Ioi 1, Real.log t * rexp (-(al * ((NN p : ℤ) : ℝ)) * t)
      ≤ ((NN p : ℤ) : ℝ) *
        (rexp (-(al * ((NN p : ℤ) : ℝ))) / (al * ((NN p : ℤ) : ℝ)) ^ 2) :=
        mul_le_mul hw hJ hJnn hN0.le
    _ = rexp (-(al * ((NN p : ℤ) : ℝ))) / (al ^ 2 * ((NN p : ℤ) : ℝ)) := by
        field_simp
    _ ≤ rexp (-(al * ((NN p : ℤ) : ℝ))) / (al ^ 2 * c) := by
        refine div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) ?_
        nlinarith
    _ = (1 / (c * al ^ 2)) * gauss p := by
        rw [hgauss]
        field_simp

private lemma summable_norm_integrals :
    Summable fun p : ℤ × ℤ => ∫ t in Ioi 1, ‖Real.log t * latTerm t p‖ := by
  refine Summable.of_nonneg_of_le
    (fun p => setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _)
    (fun p => norm_integral_le_gen p one_pos (by exact_mod_cast NN_ge_one p))
    (summable_gauss_lattice.mul_left (1 / (1 * al ^ 2)))

/-- **The interchange**: the lattice series integrates term by term against the
logarithm on the fundamental half-line. -/
private lemma interchange :
    ∑' p : ℤ × ℤ, IP p = ∫ t in Ioi 1, Real.log t * theta5 t := by
  have h := integral_tsum_of_summable_integral_norm
    (F := fun (p : ℤ × ℤ) (t : ℝ) => Real.log t * latTerm t p)
    (fun p => integrable_term p) summable_norm_integrals
  unfold IP
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  rw [tsum_mul_left, (hasSum_latTerm ht0).tsum_eq]

/-! ## 10. The three founding classes and the tail majorant -/

private lemma chi5_one_val : chi5 1 = 1 := by decide

private lemma wI_00 : wI ((0 : ℤ), (0 : ℤ)) = 1 := by
  unfold wI NN
  norm_num
  exact_mod_cast chi5_one_val

private def MM (p : ℤ × ℤ) : ℝ := if excluded p then 0 else (1 / (9 * al ^ 2)) * gauss p

private lemma MM_nonneg (p : ℤ × ℤ) : 0 ≤ MM p := by
  unfold MM
  have hα := al_pos
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by positivity) (gauss_pos p).le

private lemma MM_summable : Summable MM := by
  have hα := al_pos
  refine Summable.of_nonneg_of_le MM_nonneg (fun p => ?_)
    (summable_gauss_lattice.mul_left (1 / (9 * al ^ 2)))
  unfold MM
  split_ifs
  · exact mul_nonneg (by positivity) (gauss_pos p).le
  · exact le_rfl

private lemma IP_abs_le_MM {p : ℤ × ℤ} (hp : p ≠ ((0 : ℤ), (0 : ℤ))) : |IP p| ≤ MM p := by
  by_cases hw : wI p = 0
  · have hz : IP p = 0 := by
      unfold IP
      rw [setIntegral_congr_fun (g := fun _ : ℝ => (0 : ℝ)) measurableSet_Ioi
        (fun t _ => by rw [latTerm_form, hw]; ring)]
      simp
    rw [hz, abs_zero]
    exact MM_nonneg p
  · have hchi : chi5 (NN p) ≠ 0 := by
      intro h
      apply hw
      unfold wI
      rw [h]
      push_cast
      ring
    have hnot : ¬ excluded p := by
      intro hex
      rcases hex with h | h | h
      · exact hp h
      · apply hchi
        rw [h]
        rw [show NN ((0 : ℤ), (1 : ℤ)) = 5 from by unfold NN; ring]
        exact chi5_five
      · apply hchi
        rw [h]
        rw [show NN ((0 : ℤ), (-1 : ℤ)) = 5 from by unfold NN; ring]
        exact chi5_five
    have hN9 : (9 : ℝ) ≤ ((NN p : ℤ) : ℝ) := by exact_mod_cast NN_ge_nine hp hchi
    unfold MM
    rw [if_neg hnot]
    have h1 : |IP p| ≤ ∫ t in Ioi 1, ‖Real.log t * latTerm t p‖ := by
      have := norm_integral_le_integral_norm (μ := volume.restrict (Ioi 1))
        (f := fun t => Real.log t * latTerm t p)
      rwa [Real.norm_eq_abs] at this
    refine h1.trans ?_
    have := norm_integral_le_gen p (show (0:ℝ) < 9 by norm_num) hN9
    calc ∫ t in Ioi 1, ‖Real.log t * latTerm t p‖
        ≤ (1 / (9 * al ^ 2)) * gauss p := this
      _ = 1 / (9 * al ^ 2) * gauss p := by ring

/-! ## 11. The strict positivity -/

set_option maxHeartbeats 2000000 in
/-- **The odd sector's first moment is strictly positive**:
`0 < ∫₁^∞ θ₅(t)·log t dt`, by certified exact arithmetic — the founding class
dominates the entire remaining lattice population with margin. -/
theorem theOddMomentIsPositive : 0 < ∫ t in Ioi 1, Real.log t * theta5 t := by
  have hα := al_pos
  rw [← interchange]
  have hIP_sum : Summable IP := by
    refine Summable.of_norm_bounded summable_norm_integrals fun p => ?_
    exact norm_integral_le_integral_norm _
  have hsplit := hIP_sum.tsum_eq_add_tsum_ite ((0, 0) : ℤ × ℤ)
  -- the founding class
  have hIP0 : (5109 : ℝ) / 2222 ≤ IP ((0 : ℤ), (0 : ℤ)) := by
    unfold IP
    have hval : ∀ t ∈ Ioi (1 : ℝ),
        Real.log t * latTerm t ((0 : ℤ), (0 : ℤ)) = Real.log t * rexp (-al * t) := by
      intro t _
      rw [latTerm_form, wI_00,
        show ((NN ((0 : ℤ), (0 : ℤ)) : ℤ) : ℝ) = 1 from by
          rw [show NN ((0 : ℤ), (0 : ℤ)) = 1 from by unfold NN; ring]; norm_num]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi hval]
    refine le_trans ?_ J_lo
    rw [le_div_iff₀ hα]
    nlinarith [bd_m3, al_hi]
  -- the tail
  have hite_sum : Summable fun p : ℤ × ℤ => if p = ((0, 0) : ℤ × ℤ) then 0 else IP p := by
    refine Summable.of_norm_bounded hIP_sum.norm fun p => ?_
    split_ifs
    · simp
    · exact le_rfl
  have hrest : -(∑' p : ℤ × ℤ, MM p)
      ≤ ∑' p : ℤ × ℤ, (if p = ((0, 0) : ℤ × ℤ) then 0 else IP p) := by
    have hpt : ∀ p : ℤ × ℤ, -(MM p) ≤ (if p = ((0, 0) : ℤ × ℤ) then 0 else IP p) := by
      intro p
      split_ifs with h
      · linarith [MM_nonneg p]
      · linarith [(abs_le.mp (IP_abs_le_MM h)).1]
    have := MM_summable.neg.tsum_le_tsum hpt hite_sum
    calc -(∑' p : ℤ × ℤ, MM p) = ∑' p : ℤ × ℤ, -(MM p) := tsum_neg.symm
      _ ≤ _ := this
  -- the majorant total
  have hMM_total : ∑' p : ℤ × ℤ, MM p
      ≤ (1 / (9 * al ^ 2)) *
        (((8012 : ℝ) / 10000 + 2 * ((4840 : ℝ) / 1000) *
            (((315 : ℝ) / 10000) / (1 - (315 : ℝ) / 10000))) *
          (1 + 2 * ((2450 : ℝ) / 1000) *
            (((1734 : ℝ) / 10000) / (1 - (1734 : ℝ) / 10000)))
          - (8004 : ℝ) / 10000 - 2 * ((3255 : ℝ) / 10000)) := by
    -- the excluded-class Gaussian
    have hgauss_split : ∀ p : ℤ × ℤ, MM p
        ≤ (1 / (9 * al ^ 2)) * (if excluded p then 0 else gauss p) := by
      intro p
      unfold MM
      split_ifs
      · simp
      · exact le_rfl
    have hf'_summable : Summable fun p : ℤ × ℤ => if excluded p then 0 else gauss p := by
      refine Summable.of_norm_bounded summable_gauss_lattice.norm fun p => ?_
      split_ifs
      · simp only [norm_zero]
        exact norm_nonneg _
      · exact le_rfl
    have hM1 : ∑' p : ℤ × ℤ, MM p
        ≤ (1 / (9 * al ^ 2)) * ∑' p : ℤ × ℤ, (if excluded p then 0 else gauss p) := by
      have := MM_summable.tsum_le_tsum hgauss_split (hf'_summable.mul_left (1 / (9 * al ^ 2)))
      rwa [tsum_mul_left] at this
    have h3fun : ∀ p : ℤ × ℤ, (if excluded p then 0 else gauss p)
        = gauss p - (if excluded p then gauss p else 0) := by
      intro p
      split_ifs <;> ring
    have h3_summable : Summable fun p : ℤ × ℤ => if excluded p then gauss p else 0 := by
      refine Summable.of_norm_bounded summable_gauss_lattice.norm fun p => ?_
      split_ifs
      · exact le_rfl
      · simp only [norm_zero]
        exact norm_nonneg _
    have h3val : ∑' p : ℤ × ℤ, (if excluded p then gauss p else 0)
        = gauss ((0 : ℤ), (0 : ℤ)) + gauss ((0 : ℤ), (1 : ℤ)) + gauss ((0 : ℤ), (-1 : ℤ)) := by
      have hS : ∀ p : ℤ × ℤ,
          p ∉ ({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ))} :
            Finset (ℤ × ℤ)) → (if excluded p then gauss p else 0) = 0 := by
        intro p hp
        rw [if_neg]
        intro hex
        apply hp
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hex with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      rw [tsum_eq_sum hS]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      have e1 : excluded ((0 : ℤ), (0 : ℤ)) := Or.inl rfl
      have e2 : excluded ((0 : ℤ), (1 : ℤ)) := Or.inr (Or.inl rfl)
      have e3 : excluded ((0 : ℤ), (-1 : ℤ)) := Or.inr (Or.inr rfl)
      rw [if_pos e1, if_pos e2, if_pos e3]
      ring
    have hGsum : ∑' p : ℤ × ℤ, (if excluded p then 0 else gauss p)
        = (∑' p : ℤ × ℤ, gauss p)
          - (gauss ((0 : ℤ), (0 : ℤ)) + gauss ((0 : ℤ), (1 : ℤ)) +
              gauss ((0 : ℤ), (-1 : ℤ))) := by
      rw [← h3val]
      rw [tsum_congr h3fun]
      exact summable_gauss_lattice.tsum_sub h3_summable
    have hGbound : ∑' p : ℤ × ℤ, gauss p
        ≤ ((8012 : ℝ) / 10000 + 2 * ((4840 : ℝ) / 1000) *
            (((315 : ℝ) / 10000) / (1 - (315 : ℝ) / 10000))) *
          (1 + 2 * ((2450 : ℝ) / 1000) *
            (((1734 : ℝ) / 10000) / (1 - (1734 : ℝ) / 10000))) := by
      rw [tsum_gauss_eq]
      have hA0 : 0 ≤ ∑' k : ℤ, rexp (-al * (((4 * k + 1) ^ 2 : ℤ) : ℝ)) :=
        tsum_nonneg fun k => (Real.exp_pos _).le
      have hB0 : 0 ≤ ∑' l : ℤ, rexp (-(4 * al) * ((l ^ 2 : ℤ) : ℝ)) :=
        tsum_nonneg fun l => (Real.exp_pos _).le
      refine mul_le_mul boundA boundB hB0 ?_
      nlinarith [boundA]
    have hexcl : gauss ((0 : ℤ), (0 : ℤ)) + gauss ((0 : ℤ), (1 : ℤ)) +
        gauss ((0 : ℤ), (-1 : ℤ)) ≥ (8004 : ℝ) / 10000 + 2 * ((3255 : ℝ) / 10000) := by
      rw [gauss_value_00, gauss_value_01, gauss_value_0m1]
      linarith [bd_m1, bd_m5]
    refine hM1.trans ?_
    rw [hGsum]
    have hcoef : (0 : ℝ) ≤ 1 / (9 * al ^ 2) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    linarith [hGbound, hexcl]
  -- close the ledger
  have hcoef_bd : (1 : ℝ) / (9 * al ^ 2) ≤ 1 / (9 * ((2221 : ℝ) / 10000) ^ 2) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    nlinarith [al_lo]
  have hT_nonneg : (0 : ℝ) ≤ ((8012 : ℝ) / 10000 + 2 * ((4840 : ℝ) / 1000) *
      (((315 : ℝ) / 10000) / (1 - (315 : ℝ) / 10000))) *
        (1 + 2 * ((2450 : ℝ) / 1000) *
          (((1734 : ℝ) / 10000) / (1 - (1734 : ℝ) / 10000)))
        - (8004 : ℝ) / 10000 - 2 * ((3255 : ℝ) / 10000) := by norm_num
  have hMM_final : ∑' p : ℤ × ℤ, MM p ≤ (1 / (9 * ((2221 : ℝ) / 10000) ^ 2)) *
      (((8012 : ℝ) / 10000 + 2 * ((4840 : ℝ) / 1000) *
          (((315 : ℝ) / 10000) / (1 - (315 : ℝ) / 10000))) *
        (1 + 2 * ((2450 : ℝ) / 1000) *
          (((1734 : ℝ) / 10000) / (1 - (1734 : ℝ) / 10000)))
        - (8004 : ℝ) / 10000 - 2 * ((3255 : ℝ) / 10000)) := by
    refine hMM_total.trans ?_
    exact mul_le_mul_of_nonneg_right hcoef_bd hT_nonneg
  rw [hsplit]
  have hnum : (0 : ℝ) < (5109 : ℝ) / 2222 - (1 / (9 * ((2221 : ℝ) / 10000) ^ 2)) *
      (((8012 : ℝ) / 10000 + 2 * ((4840 : ℝ) / 1000) *
          (((315 : ℝ) / 10000) / (1 - (315 : ℝ) / 10000))) *
        (1 + 2 * ((2450 : ℝ) / 1000) *
          (((1734 : ℝ) / 10000) / (1 - (1734 : ℝ) / 10000)))
        - (8004 : ℝ) / 10000 - 2 * ((3255 : ℝ) / 10000)) := by norm_num
  linarith [hIP0, hrest, hMM_final]

/-- **The derivative does not vanish**: `Λ₅′(1) ≠ 0`.  With `Λ₅(1) = 0`
(`theOddHandForcesTheCentralVanishingAtFive`), the analytic order of the completed
L-function at the center of its odd reflection is exactly one — the analytic half of
the rank-one coincidence at five, with no Gross–Zagier input. -/
theorem theDerivativeDoesNotVanishAtFive : deriv lambda5 1 ≠ 0 := by
  rw [theDerivativeIsTheOddSectorFirstMoment]
  have hre : ∫ t in Ioi (1 : ℝ), ((Real.log t * theta5 t : ℝ) : ℂ)
      = (((∫ t in Ioi (1 : ℝ), Real.log t * theta5 t : ℝ)) : ℂ) := integral_ofReal
  rw [hre]
  intro h
  have h3 : ((∫ t in Ioi (1 : ℝ), Real.log t * theta5 t : ℝ) : ℂ) = 0 :=
    (mul_eq_zero.mp h).resolve_left (by norm_num)
  have h4 : (∫ t in Ioi (1 : ℝ), Real.log t * theta5 t) = (0 : ℝ) := by exact_mod_cast h3
  exact absurd h4 (ne_of_gt theOddMomentIsPositive)

end Soma.Holonics.Millennium.FivePositivity
