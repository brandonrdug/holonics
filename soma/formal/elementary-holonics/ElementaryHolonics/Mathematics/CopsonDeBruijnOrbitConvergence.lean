import ElementaryHolonics.Mathematics.CopsonDeBruijnNormalizedDynamics

/-!
# Compactness and trapping preparation for the normalized Copson--de Bruijn orbit

This file begins the global orbit argument from the exact normalized drift owner.  It returns an
explicit uniform upper bound and the eventual strict source-offset separation needed to use the
moving-root drift laws without an extra hypothesis.

The remaining seam is a genuine global trapping theorem: after the moving roots exist and the
source offset has separated, the orbit must either enter the expanding root interval or remain on
one exterior side; the harmonic-size exact drift must then exclude any limiting point away from a
limiting root.  No convergence or desired limit is stored as a field or assumed here.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set Filter Topology

/-- On the admissible ray, removing one unit under the principal square root cannot increase a
recurrence value. -/
theorem sqrt_sq_sub_one_le_self {u : ℝ} (hu : 1 ≤ u) :
    Real.sqrt (u ^ 2 - 1) ≤ u := by
  rw [Real.sqrt_le_left (zero_le_one.trans hu)]
  linarith

/-- The exact square-root-scale inequality which closes the uniform orbit bound. -/
theorem one_div_sqrt_add_two_sqrt_succ_le_two_sqrt_add_two (n : ℕ) :
    1 / Real.sqrt (n + 2 : ℝ) + 2 * Real.sqrt (n + 1 : ℝ) ≤
      2 * Real.sqrt (n + 2 : ℝ) := by
  let a := Real.sqrt (n + 2 : ℝ)
  let b := Real.sqrt (n + 1 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have haSq : a ^ 2 = (n + 2 : ℝ) := by
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  have hbSq : b ^ 2 = (n + 1 : ℝ) := by
    dsimp [b]
    rw [Real.sq_sqrt]
    positivity
  change 1 / a + 2 * b ≤ 2 * a
  have hone : 1 / a ≤ 2 * a - 2 * b := by
    rw [div_le_iff₀ ha]
    nlinarith [sq_nonneg (a - b)]
  linarith

/-- Every globally admissible raw orbit is bounded above by `2x sqrt(n+1)`. -/
theorem realRecurrenceValue_le_two_mul_sqrt {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) : ∀ n : ℕ,
    realRecurrenceValue x n ≤ 2 * x * Real.sqrt (n + 1 : ℝ)
  | 0 => by
      have hx : 1 ≤ x := by
        rw [← recurrence.initial]
        exact (recurrence.iterate 0).2
      simp
      linarith
  | n + 1 => by
      rw [realRecurrenceValue_succ]
      have hraw : 1 ≤ realRecurrenceValue x n := by
        rw [← recurrence.iterate_eq_realRecurrenceValue n]
        exact (recurrence.iterate n).2
      have hsqrt := sqrt_sq_sub_one_le_self hraw
      have hinduction := realRecurrenceValue_le_two_mul_sqrt recurrence n
      have hxOne : 1 ≤ x := by
        rw [← recurrence.initial]
        exact (recurrence.iterate 0).2
      have hx : 0 < x := zero_lt_one.trans_le hxOne
      have hscale := one_div_sqrt_add_two_sqrt_succ_le_two_sqrt_add_two n
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n + 2 : ℝ) := by
        norm_num
        ring
      rw [hcast]
      calc
        x / Real.sqrt (n + 2 : ℝ) + Real.sqrt (realRecurrenceValue x n ^ 2 - 1)
            ≤ x / Real.sqrt (n + 2 : ℝ) + realRecurrenceValue x n :=
          add_le_add le_rfl hsqrt
        _ ≤ x / Real.sqrt (n + 2 : ℝ) +
              2 * x * Real.sqrt (n + 1 : ℝ) := add_le_add le_rfl hinduction
        _ = x * (1 / Real.sqrt (n + 2 : ℝ) +
              2 * Real.sqrt (n + 1 : ℝ)) := by ring
        _ ≤ x * (2 * Real.sqrt (n + 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hscale hx.le
        _ = 2 * x * Real.sqrt (n + 2 : ℝ) := by ring

/-- The normalized orbit therefore lies in the fixed compact interval `(0, 2x]`. -/
theorem normalizedRecurrenceValue_le_two_mul {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    normalizedRecurrenceValue x n ≤ 2 * x := by
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  rw [normalizedRecurrenceValue, div_le_iff₀ hsqrt]
  simpa [mul_assoc] using realRecurrenceValue_le_two_mul_sqrt recurrence n

/-- On the fixed compact orbit interval, the exact quotient drift has a uniform harmonic-scale
lower bound whenever its quadratic stays separated from zero. -/
theorem normalizedDrift_compact_lower_bound {x : ℝ} (hx : 1 < x)
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ)
    (hoffset : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n) :
    |normalizedDriftQuadratic x n (normalizedRecurrenceValue x n)| /
        (4 * x * (n + 2 : ℝ)) ≤
      |normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n| := by
  let factor := normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
    2 * x / (n + 2 : ℝ)
  let denom := (n + 2 : ℝ) * factor
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hnewOffset : 0 ≤ normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ) := by
    rw [normalizedRecurrenceValue_succ_sub_source recurrence]
    exact Real.sqrt_nonneg _
  have hfactor : 0 < factor := by
    dsimp [factor]
    rw [show normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
        2 * x / (n + 2 : ℝ) =
      (normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ)) +
        (normalizedRecurrenceValue x n - x / (n + 2 : ℝ)) by ring]
    exact add_pos_of_nonneg_of_pos hnewOffset (sub_pos.mpr hoffset)
  have hdenom : 0 < denom := mul_pos (by positivity) hfactor
  have hfactorUpper : factor ≤ 4 * x := by
    dsimp [factor]
    have hcurrent := normalizedRecurrenceValue_le_two_mul recurrence n
    have hnext := normalizedRecurrenceValue_le_two_mul recurrence (n + 1)
    have hsource : 0 ≤ 2 * x / (n + 2 : ℝ) := by positivity
    linarith
  have hdenomUpper : denom ≤ 4 * x * (n + 2 : ℝ) := by
    dsimp [denom]
    nlinarith [show (0 : ℝ) ≤ n + 2 by positivity]
  have hlargeDenom : 0 < 4 * x * (n + 2 : ℝ) := by positivity
  rw [normalizedRecurrenceValue_drift_eq recurrence n hoffset, abs_div, abs_neg,
    abs_of_pos hdenom]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hdenom hdenomUpper

/-- Once `x² < n+2`, the source offset is below the elementary admissibility floor. -/
theorem sourceOffset_lt_one_div_sqrt {x : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hscale : x ^ 2 < (n + 2 : ℝ)) :
    x / (n + 2 : ℝ) < 1 / Real.sqrt (n + 1 : ℝ) := by
  have hsqrtNext : 0 < Real.sqrt (n + 2 : ℝ) := by positivity
  have hsqrtCurrent : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hxSqrt : x < Real.sqrt (n + 2 : ℝ) := by
    rw [← Real.sqrt_sq hx, Real.sqrt_lt_sqrt_iff (sq_nonneg x)]
    exact hscale
  have hfirst : x / (n + 2 : ℝ) < 1 / Real.sqrt (n + 2 : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < n + 2) hsqrtNext]
    calc
      x * Real.sqrt (n + 2 : ℝ) <
          Real.sqrt (n + 2 : ℝ) * Real.sqrt (n + 2 : ℝ) :=
        mul_lt_mul_of_pos_right hxSqrt hsqrtNext
      _ = 1 * (n + 2 : ℝ) := by
        rw [← pow_two, Real.sq_sqrt (by positivity)]
        ring
  have hsqrtLt : Real.sqrt (n + 1 : ℝ) < Real.sqrt (n + 2 : ℝ) :=
    Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  exact hfirst.trans (one_div_lt_one_div_of_lt hsqrtCurrent hsqrtLt)

/-- Every admissible orbit eventually lies strictly beyond its normalized source offset. -/
theorem eventually_sourceOffset_lt_normalizedRecurrenceValue {x : ℝ}
    (hx : 0 ≤ x) (recurrence : AdmissibleRealRecurrence x) :
    ∀ᶠ n : ℕ in atTop,
      x / ((n : ℝ) + 2) < normalizedRecurrenceValue x n := by
  have hscale : ∀ᶠ n : ℕ in atTop, x ^ 2 < (n : ℝ) + 2 := by
    have hnat := tendsto_natCast_atTop_atTop.eventually_gt_atTop (x ^ 2)
    filter_upwards [hnat] with n hn
    linarith
  filter_upwards [hscale] with n hn
  exact (sourceOffset_lt_one_div_sqrt hx hn).trans_le
    (one_div_sqrt_nat_succ_le_normalizedRecurrenceValue recurrence n)

/-- The normalized orbit is eventually in the exact region where both moving-root drift
equivalences apply. -/
theorem eventually_normalized_dynamics_region {x : ℝ} (hx : 1 < x)
    (recurrence : AdmissibleRealRecurrence x) :
    ∀ᶠ n : ℕ in atTop,
      x / ((n : ℝ) + 2) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n :=
  (eventually_sourceOffset_lt_normalizedRecurrenceValue (zero_le_one.trans hx.le) recurrence).and
    (eventually_normalizedDiscriminant_pos hx)

section Audit

#print axioms realRecurrenceValue_le_two_mul_sqrt
#print axioms normalizedRecurrenceValue_le_two_mul
#print axioms normalizedDrift_compact_lower_bound
#print axioms sourceOffset_lt_one_div_sqrt
#print axioms eventually_sourceOffset_lt_normalizedRecurrenceValue
#print axioms eventually_normalized_dynamics_region

end Audit

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
