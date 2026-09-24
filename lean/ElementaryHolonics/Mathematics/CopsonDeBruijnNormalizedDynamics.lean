import ElementaryHolonics.Mathematics.CopsonDeBruijnAdmissibleRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Normalized Copson--de Bruijn recurrence dynamics

The raw recurrence grows on the square-root scale.  This owner divides its `(n+1)`st mathematical
iterate by `sqrt (n+1)`, derives the exact normalized step and its finite drift roots, and isolates
the trapping and branch-selection obligations needed for the two de Bruijn asymptotic branches.

No convergence or desired limit is stored in a carrier.  Every use of a principal square root is
guarded by the admissible recurrence or an explicit nonnegative discriminant.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set Filter Topology
open scoped NNReal ENNReal

/-- The zero-based normalized recurrence; index `n` is mathematical index `n+1`. -/
def normalizedRecurrenceValue (x : ℝ) (n : ℕ) : ℝ :=
  realRecurrenceValue x n / Real.sqrt (n + 1 : ℝ)

/-- The two formal roots of the limiting drift polynomial. -/
def lowerAsymptoticRoot (x : ℝ) : ℝ :=
  x - Real.sqrt (x ^ 2 - 1)

def upperAsymptoticRoot (x : ℝ) : ℝ :=
  x + Real.sqrt (x ^ 2 - 1)

/-- The finite-index discriminant of the normalized fixed-point equation. -/
def normalizedDiscriminant (x : ℝ) (n : ℕ) : ℝ :=
  x ^ 2 - 1 - x ^ 2 / (n + 2 : ℝ)

/-- The moving lower and upper roots of the exact normalized drift polynomial. -/
def lowerDriftRoot (x : ℝ) (n : ℕ) : ℝ :=
  x - Real.sqrt (normalizedDiscriminant x n)

def upperDriftRoot (x : ℝ) (n : ℕ) : ℝ :=
  x + Real.sqrt (normalizedDiscriminant x n)

theorem realRecurrenceValue_eq_sqrt_mul_normalized (x : ℝ) (n : ℕ) :
    realRecurrenceValue x n =
      Real.sqrt (n + 1 : ℝ) * normalizedRecurrenceValue x n := by
  rw [normalizedRecurrenceValue]
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  field_simp

/-- Admissibility makes every normalized value positive. -/
theorem normalizedRecurrenceValue_pos {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    0 < normalizedRecurrenceValue x n := by
  rw [normalizedRecurrenceValue]
  have hraw : 1 ≤ realRecurrenceValue x n := by
    rw [← recurrence.iterate_eq_realRecurrenceValue n]
    exact (recurrence.iterate n).2
  exact div_pos (zero_lt_one.trans_le hraw) (by positivity)

/-- The raw square is the scale times the normalized square. -/
theorem realRecurrenceValue_sq_eq_scale_mul_normalized_sq (x : ℝ) (n : ℕ) :
    realRecurrenceValue x n ^ 2 =
      (n + 1 : ℝ) * normalizedRecurrenceValue x n ^ 2 := by
  rw [realRecurrenceValue_eq_sqrt_mul_normalized, mul_pow,
    Real.sq_sqrt (by positivity)]

/-- The exact normalized recurrence step. -/
theorem normalizedRecurrenceValue_succ {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    normalizedRecurrenceValue x (n + 1) =
      x / (n + 2 : ℝ) +
        Real.sqrt (((n + 1 : ℝ) * normalizedRecurrenceValue x n ^ 2 - 1) /
          (n + 2 : ℝ)) := by
  rw [normalizedRecurrenceValue, realRecurrenceValue_succ]
  have hsqrt : 0 < Real.sqrt (n + 2 : ℝ) := by positivity
  have hscale : Real.sqrt (n + 2 : ℝ) ^ 2 = (n + 2 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hradicand : 0 ≤ realRecurrenceValue x n ^ 2 - 1 := by
    have hraw : 1 ≤ realRecurrenceValue x n := by
      rw [← recurrence.iterate_eq_realRecurrenceValue n]
      exact (recurrence.iterate n).2
    nlinarith [sq_nonneg (realRecurrenceValue x n - 1)]
  have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n + 2 : ℝ) := by
    norm_num
    ring
  rw [hcast]
  rw [add_div]
  have hxpart : x / Real.sqrt (n + 2 : ℝ) / Real.sqrt (n + 2 : ℝ) =
      x / (n + 2 : ℝ) := by
    rw [div_div, ← pow_two, hscale]
  rw [hxpart, ← Real.sqrt_div hradicand]
  congr 2
  rw [realRecurrenceValue_sq_eq_scale_mul_normalized_sq]

/-- Removing the entering source term leaves the exact nonnegative root current. -/
theorem normalizedRecurrenceValue_succ_sub_source {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ) =
      Real.sqrt (((n + 1 : ℝ) * normalizedRecurrenceValue x n ^ 2 - 1) /
        (n + 2 : ℝ)) := by
  rw [normalizedRecurrenceValue_succ recurrence]
  ring

/-- Squaring the normalized step is lawful because the right side is the principal root. -/
theorem normalizedRecurrenceValue_succ_sub_source_sq {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    (normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ)) ^ 2 =
      ((n + 1 : ℝ) * normalizedRecurrenceValue x n ^ 2 - 1) /
        (n + 2 : ℝ) := by
  rw [normalizedRecurrenceValue_succ_sub_source recurrence]
  rw [Real.sq_sqrt]
  have hraw := recurrence.radicand_nonnegative n
  rw [recurrence.iterate_eq_realRecurrenceValue] at hraw
  rw [realRecurrenceValue_sq_eq_scale_mul_normalized_sq] at hraw
  exact div_nonneg hraw (by positivity)

/-! ## Moving roots of the exact drift -/

/-- The exact quadratic whose sign determines normalized drift. -/
def normalizedDriftQuadratic (x : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  z ^ 2 - 2 * x * z + 1 + x ^ 2 / (n + 2 : ℝ)

theorem normalizedDriftQuadratic_factor {x : ℝ} {n : ℕ}
    (hdisc : 0 ≤ normalizedDiscriminant x n) (z : ℝ) :
    normalizedDriftQuadratic x n z =
      (z - lowerDriftRoot x n) * (z - upperDriftRoot x n) := by
  have hsqrt := Real.sq_sqrt hdisc
  unfold normalizedDriftQuadratic lowerDriftRoot upperDriftRoot normalizedDiscriminant at *
  nlinarith

theorem lowerDriftRoot_le_upperDriftRoot (x : ℝ) (n : ℕ) :
    lowerDriftRoot x n ≤ upperDriftRoot x n := by
  unfold lowerDriftRoot upperDriftRoot
  have := Real.sqrt_nonneg (normalizedDiscriminant x n)
  linarith

theorem lowerDriftRoot_lt_upperDriftRoot {x : ℝ} {n : ℕ}
    (hdisc : 0 < normalizedDiscriminant x n) :
    lowerDriftRoot x n < upperDriftRoot x n := by
  unfold lowerDriftRoot upperDriftRoot
  have := Real.sqrt_pos.2 hdisc
  linarith

/-- Between the two genuine moving roots, and only there, the exact drift polynomial is negative. -/
theorem normalizedDriftQuadratic_neg_iff_between {x : ℝ} {n : ℕ}
    (hdisc : 0 < normalizedDiscriminant x n) (z : ℝ) :
    normalizedDriftQuadratic x n z < 0 ↔
      lowerDriftRoot x n < z ∧ z < upperDriftRoot x n := by
  rw [normalizedDriftQuadratic_factor hdisc.le]
  constructor
  · intro hproduct
    rcases (mul_neg_iff.mp hproduct) with hbetween | himpossible
    · exact ⟨sub_pos.mp hbetween.1, sub_neg.mp hbetween.2⟩
    · have horder := lowerDriftRoot_lt_upperDriftRoot hdisc
      exfalso
      linarith [sub_neg.mp himpossible.1, sub_pos.mp himpossible.2]
  · rintro ⟨hlower, hupper⟩
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hlower) (sub_neg.mpr hupper)

/-- Difference of squares turns the normalized recurrence into an exact quantitative drift law. -/
theorem normalizedRecurrenceValue_drift_identity {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    (n + 2 : ℝ) *
        ((normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
          (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
            2 * x / (n + 2 : ℝ))) =
      -normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) := by
  have hsquare := normalizedRecurrenceValue_succ_sub_source_sq recurrence n
  have hscale : (0 : ℝ) < n + 2 := by positivity
  calc
    (n + 2 : ℝ) *
        ((normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
          (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
            2 * x / (n + 2 : ℝ))) =
      (n + 2 : ℝ) *
        ((normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ)) ^ 2 -
          (normalizedRecurrenceValue x n - x / (n + 2 : ℝ)) ^ 2) := by ring
    _ = (n + 2 : ℝ) *
        ((((n + 1 : ℝ) * normalizedRecurrenceValue x n ^ 2 - 1) /
          (n + 2 : ℝ)) -
          (normalizedRecurrenceValue x n - x / (n + 2 : ℝ)) ^ 2) := by rw [hsquare]
    _ = -normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) := by
      unfold normalizedDriftQuadratic
      field_simp [hscale.ne']
      ring

/-- Once the old normalized value lies strictly beyond the source offset, the drift has exactly
the opposite sign from its quadratic. -/
theorem normalizedRecurrenceValue_drift_pos_iff_quadratic_neg {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ)
    (hoffset : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n) :
    normalizedRecurrenceValue x n < normalizedRecurrenceValue x (n + 1) ↔
      normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) < 0 := by
  have hidentity := normalizedRecurrenceValue_drift_identity recurrence n
  have hscale : 0 < (n + 2 : ℝ) := by positivity
  have hnewOffset : 0 ≤ normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ) := by
    rw [normalizedRecurrenceValue_succ_sub_source recurrence]
    exact Real.sqrt_nonneg _
  have hfactor : 0 < normalizedRecurrenceValue x (n + 1) +
      normalizedRecurrenceValue x n - 2 * x / (n + 2 : ℝ) := by
    rw [show normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
        2 * x / (n + 2 : ℝ) =
      (normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ)) +
        (normalizedRecurrenceValue x n - x / (n + 2 : ℝ)) by ring]
    exact add_pos_of_nonneg_of_pos hnewOffset (sub_pos.mpr hoffset)
  constructor
  · intro hdrift
    have hpositive : 0 < (n + 2 : ℝ) *
        ((normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
          (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
            2 * x / (n + 2 : ℝ))) :=
      mul_pos hscale (mul_pos (sub_pos.mpr hdrift) hfactor)
    rw [hidentity] at hpositive
    linarith
  · intro hquadratic
    have hpositive : 0 < (n + 2 : ℝ) *
        ((normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
          (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
            2 * x / (n + 2 : ℝ))) := by
      rw [hidentity]
      linarith
    have hpair : 0 <
        (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
          (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
            2 * x / (n + 2 : ℝ)) := by
      rcases mul_pos_iff.mp hpositive with hgood | hbad
      · exact hgood.2
      · exact False.elim ((not_lt_of_ge hscale.le) hbad.1)
    rcases mul_pos_iff.mp hpair with hgood | hbad
    · exact sub_pos.mp hgood.1
    · exact False.elim ((not_lt_of_ge hfactor.le) hbad.2)

/-- The quantitative drift is the negative drift polynomial divided by the positive local scale.
This is the exact `1/(n+2)`-sized current needed by any later trapping argument. -/
theorem normalizedRecurrenceValue_drift_eq {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ)
    (hoffset : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n) :
    normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n =
      -normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) /
        ((n + 2 : ℝ) *
          (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
            2 * x / (n + 2 : ℝ))) := by
  have hnewOffset : 0 ≤ normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ) := by
    rw [normalizedRecurrenceValue_succ_sub_source recurrence]
    exact Real.sqrt_nonneg _
  have hfactor : 0 < normalizedRecurrenceValue x (n + 1) +
      normalizedRecurrenceValue x n - 2 * x / (n + 2 : ℝ) := by
    rw [show normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
        2 * x / (n + 2 : ℝ) =
      (normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ)) +
        (normalizedRecurrenceValue x n - x / (n + 2 : ℝ)) by ring]
    exact add_pos_of_nonneg_of_pos hnewOffset (sub_pos.mpr hoffset)
  have hdenom : 0 < (n + 2 : ℝ) *
      (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
        2 * x / (n + 2 : ℝ)) := mul_pos (by positivity) hfactor
  rw [eq_div_iff hdenom.ne']
  have hidentity := normalizedRecurrenceValue_drift_identity recurrence n
  simpa [mul_assoc, mul_left_comm, mul_comm] using hidentity

/-- In the genuine-root region, normalized current rises exactly between the moving roots. -/
theorem normalizedRecurrenceValue_drift_pos_iff_between {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ)
    (hoffset : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n)
    (hdisc : 0 < normalizedDiscriminant x n) :
    normalizedRecurrenceValue x n < normalizedRecurrenceValue x (n + 1) ↔
      lowerDriftRoot x n < normalizedRecurrenceValue x n ∧
        normalizedRecurrenceValue x n < upperDriftRoot x n := by
  rw [normalizedRecurrenceValue_drift_pos_iff_quadratic_neg recurrence n hoffset,
    normalizedDriftQuadratic_neg_iff_between hdisc]

theorem normalizedDriftQuadratic_pos_iff_outside {x : ℝ} {n : ℕ}
    (hdisc : 0 < normalizedDiscriminant x n) (z : ℝ) :
    0 < normalizedDriftQuadratic x n z ↔
      z < lowerDriftRoot x n ∨ upperDriftRoot x n < z := by
  rw [normalizedDriftQuadratic_factor hdisc.le]
  constructor
  · intro hproduct
    rcases mul_pos_iff.mp hproduct with habove | hbelow
    · exact Or.inr (sub_pos.mp habove.2)
    · exact Or.inl (sub_neg.mp hbelow.1)
  · rintro (hlower | hupper)
    · have horder := lowerDriftRoot_lt_upperDriftRoot hdisc
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hlower) (sub_neg.mpr (hlower.trans horder))
    · have horder := lowerDriftRoot_lt_upperDriftRoot hdisc
      exact mul_pos (sub_pos.mpr (horder.trans hupper)) (sub_pos.mpr hupper)

/-- Outside the moving-root interval the normalized current decreases strictly. -/
theorem normalizedRecurrenceValue_drift_neg_iff_outside {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ)
    (hoffset : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n)
    (hdisc : 0 < normalizedDiscriminant x n) :
    normalizedRecurrenceValue x (n + 1) < normalizedRecurrenceValue x n ↔
      normalizedRecurrenceValue x n < lowerDriftRoot x n ∨
        upperDriftRoot x n < normalizedRecurrenceValue x n := by
  have hidentity := normalizedRecurrenceValue_drift_identity recurrence n
  have hscale : 0 < (n + 2 : ℝ) := by positivity
  have hnewOffset : 0 ≤ normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ) := by
    rw [normalizedRecurrenceValue_succ_sub_source recurrence]
    exact Real.sqrt_nonneg _
  have hfactor : 0 < normalizedRecurrenceValue x (n + 1) +
      normalizedRecurrenceValue x n - 2 * x / (n + 2 : ℝ) := by
    rw [show normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
        2 * x / (n + 2 : ℝ) =
      (normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ)) +
        (normalizedRecurrenceValue x n - x / (n + 2 : ℝ)) by ring]
    exact add_pos_of_nonneg_of_pos hnewOffset (sub_pos.mpr hoffset)
  have hsign : normalizedRecurrenceValue x (n + 1) < normalizedRecurrenceValue x n ↔
      0 < normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) := by
    constructor
    · intro hdecrease
      have hnegative : (n + 2 : ℝ) *
          ((normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
            (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
              2 * x / (n + 2 : ℝ))) < 0 :=
        mul_neg_of_pos_of_neg hscale (mul_neg_of_neg_of_pos (sub_neg.mpr hdecrease) hfactor)
      rw [hidentity] at hnegative
      linarith
    · intro hquadratic
      have hnegative : (n + 2 : ℝ) *
          ((normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
            (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
              2 * x / (n + 2 : ℝ))) < 0 := by
        rw [hidentity]
        linarith
      have hpair :
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) *
            (normalizedRecurrenceValue x (n + 1) + normalizedRecurrenceValue x n -
              2 * x / (n + 2 : ℝ)) < 0 := by
        rcases mul_neg_iff.mp hnegative with hgood | hbad
        · exact hgood.2
        · exact False.elim ((not_lt_of_ge hscale.le) hbad.1)
      rcases mul_neg_iff.mp hpair with hbad | hgood
      · exact False.elim ((not_lt_of_ge hfactor.le) hbad.2)
      · exact sub_neg.mp hgood.1
  rw [hsign, normalizedDriftQuadratic_pos_iff_outside hdisc]

/-- The finite discriminants increase toward the limiting one. -/
theorem normalizedDiscriminant_mono (x : ℝ) : Monotone (normalizedDiscriminant x) := by
  intro n m hnm
  unfold normalizedDiscriminant
  have hden : (n + 2 : ℝ) ≤ (m + 2 : ℝ) := by exact_mod_cast Nat.add_le_add_right hnm 2
  have hfrac : x ^ 2 / (m + 2 : ℝ) ≤ x ^ 2 / (n + 2 : ℝ) :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) hden
  linarith

/-- The lower moving root decreases and the upper moving root increases with the aperture. -/
theorem lowerDriftRoot_antitone (x : ℝ) : Antitone (lowerDriftRoot x) := by
  intro n m hnm
  unfold lowerDriftRoot
  exact sub_le_sub_left (Real.sqrt_le_sqrt (normalizedDiscriminant_mono x hnm)) x

theorem upperDriftRoot_monotone (x : ℝ) : Monotone (upperDriftRoot x) := by
  intro n m hnm
  unfold upperDriftRoot
  simpa [add_comm] using
    add_le_add_left (Real.sqrt_le_sqrt (normalizedDiscriminant_mono x hnm)) x

/-! ## The moving roots reach the two claimed asymptotic candidates -/

theorem tendsto_normalizedDiscriminant (x : ℝ) :
    Tendsto (normalizedDiscriminant x) atTop (nhds (x ^ 2 - 1)) := by
  have hdiv : Tendsto (fun n : ℕ ↦ x ^ 2 / (n + 2 : ℝ)) atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hden
  change Tendsto (fun n : ℕ ↦ x ^ 2 - 1 - x ^ 2 / (n + 2 : ℝ))
    atTop (nhds (x ^ 2 - 1))
  simpa using tendsto_const_nhds.sub hdiv

/-- Above one, genuine moving roots exist at every sufficiently late aperture. -/
theorem eventually_normalizedDiscriminant_pos {x : ℝ} (hx : 1 < x) :
    ∀ᶠ n in atTop, 0 < normalizedDiscriminant x n := by
  have hlimit : 0 < x ^ 2 - 1 := by nlinarith
  exact (tendsto_normalizedDiscriminant x).eventually (Ioi_mem_nhds hlimit)

theorem tendsto_lowerDriftRoot (x : ℝ) :
    Tendsto (lowerDriftRoot x) atTop (nhds (lowerAsymptoticRoot x)) := by
  change Tendsto (fun n ↦ x - Real.sqrt (normalizedDiscriminant x n)) atTop
    (nhds (x - Real.sqrt (x ^ 2 - 1)))
  exact tendsto_const_nhds.sub (tendsto_normalizedDiscriminant x).sqrt

theorem tendsto_upperDriftRoot (x : ℝ) :
    Tendsto (upperDriftRoot x) atTop (nhds (upperAsymptoticRoot x)) := by
  change Tendsto (fun n ↦ x + Real.sqrt (normalizedDiscriminant x n)) atTop
    (nhds (x + Real.sqrt (x ^ 2 - 1)))
  exact tendsto_const_nhds.add (tendsto_normalizedDiscriminant x).sqrt

/-! ## Limiting root algebra and the remaining global seam -/

theorem lowerAsymptoticRoot_mul_upperAsymptoticRoot {x : ℝ} (hx : 1 ≤ x) :
    lowerAsymptoticRoot x * upperAsymptoticRoot x = 1 := by
  have hdisc : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hsqrt := Real.sq_sqrt hdisc
  unfold lowerAsymptoticRoot upperAsymptoticRoot
  nlinarith

theorem lowerAsymptoticRoot_lt_upperAsymptoticRoot {x : ℝ} (hx : 1 < x) :
    lowerAsymptoticRoot x < upperAsymptoticRoot x := by
  have hdisc : 0 < x ^ 2 - 1 := by nlinarith
  unfold lowerAsymptoticRoot upperAsymptoticRoot
  have := Real.sqrt_pos.2 hdisc
  linarith

theorem one_div_sqrt_nat_succ_le_normalizedRecurrenceValue {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℝ) ≤ normalizedRecurrenceValue x n := by
  rw [normalizedRecurrenceValue]
  have hraw : 1 ≤ realRecurrenceValue x n := by
    rw [← recurrence.iterate_eq_realRecurrenceValue n]
    exact (recurrence.iterate n).2
  exact div_le_div_of_nonneg_right hraw (Real.sqrt_nonneg _)

/-!
The first theorem not returned here is the global orbit-trapping statement: an admissible
normalized orbit must eventually remain in one of the two moving-root basins, and the quantitative
`normalizedRecurrenceValue_drift_eq` current must then be summed to exclude a limit outside the
limiting roots.  Only after that theorem may threshold minimality and strict coefficient transport
select the lower branch at `recurrenceThreshold` and the upper branch above it.
-/

section Audit

#print axioms normalizedRecurrenceValue_succ
#print axioms normalizedRecurrenceValue_succ_sub_source_sq
#print axioms normalizedDriftQuadratic_factor
#print axioms normalizedRecurrenceValue_drift_identity
#print axioms normalizedRecurrenceValue_drift_eq
#print axioms normalizedRecurrenceValue_drift_pos_iff_between
#print axioms normalizedRecurrenceValue_drift_neg_iff_outside
#print axioms normalizedDiscriminant_mono
#print axioms tendsto_lowerDriftRoot
#print axioms tendsto_upperDriftRoot
#print axioms lowerAsymptoticRoot_mul_upperAsymptoticRoot

end Audit

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
