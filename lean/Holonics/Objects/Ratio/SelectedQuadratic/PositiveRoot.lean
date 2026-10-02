import Holonics.Objects.Ratio.SelectedQuadratic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Order

/-! Positive selected root and the native enclosure acceptance.
The sign and order hypotheses precede every use of squared endpoints.
Real.sqrt is an exact mathematical existence witness, never a native float.
-/
namespace Holonics.Objects.Ratio.SelectedQuadratic

def EnclosureAccepted (D lower upper : ℚ) : Prop :=
  lower < upper ∧ 0 < lower ∧ 0 < upper ∧ lower ^ 2 < D ∧ D < upper ^ 2

theorem positive_root_exists {D : ℚ} (hD : 0 < D) :
    ∃ s : ℝ, 0 < s ∧ s ^ 2 = (D : ℝ) := by
  have h : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  exact ⟨Real.sqrt D, Real.sqrt_pos.mpr h, Real.sq_sqrt (le_of_lt h)⟩

theorem positive_root_unique {D : ℚ} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hsq : s ^ 2 = (D : ℝ))
    (htq : t ^ 2 = (D : ℝ)) : s = t := by
  nlinarith [sq_nonneg (s - t)]

theorem same_radicand_same_selected_root {D E : ℚ} {s t : ℝ}
    (hDE : D = E) (hs : 0 < s) (ht : 0 < t)
    (hsq : s ^ 2 = (D : ℝ)) (htq : t ^ 2 = (E : ℝ)) : s = t := by
  subst E
  exact positive_root_unique hs ht hsq htq

theorem distinct_radicands_distinct_selected_roots {D E : ℚ} {s t : ℝ}
    (hDE : D ≠ E) (hsq : s ^ 2 = (D : ℝ)) (htq : t ^ 2 = (E : ℝ)) :
    s ≠ t := by
  intro hst
  apply hDE
  apply Rat.cast_injective (α := ℝ)
  rw [← hsq, ← htq, hst]

theorem enclosure_acceptance_sound {D lower upper : ℚ} {s : ℝ}
    (ha : EnclosureAccepted D lower upper) (hs : 0 < s)
    (hsq : s ^ 2 = (D : ℝ)) : (lower : ℝ) < s ∧ s < (upper : ℝ) := by
  obtain ⟨_, hlo, hup, hlq, huq⟩ := ha
  have hl : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlo
  have hu : (0 : ℝ) < (upper : ℝ) := by exact_mod_cast hup
  have hl2 : (lower : ℝ) ^ 2 < (D : ℝ) := by exact_mod_cast hlq
  have hu2 : (D : ℝ) < (upper : ℝ) ^ 2 := by exact_mod_cast huq
  constructor <;> nlinarith

theorem enclosure_acceptance_iff {D lower upper : ℚ} {s : ℝ}
    (hs : 0 < s) (hsq : s ^ 2 = (D : ℝ)) :
    EnclosureAccepted D lower upper ↔
      0 < lower ∧ (lower : ℝ) < s ∧ s < (upper : ℝ) := by
  constructor
  · intro ha
    exact ⟨ha.2.1, enclosure_acceptance_sound ha hs hsq⟩
  · rintro ⟨hlo, hl, hu⟩
    have hl0 : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlo
    have hu0 : (0 : ℝ) < (upper : ℝ) := lt_trans hs hu
    have horder : (lower : ℝ) < (upper : ℝ) := lt_trans hl hu
    refine ⟨?_, hlo, ?_, ?_, ?_⟩
    · exact_mod_cast horder
    · exact_mod_cast hu0
    · have h : (lower : ℝ) ^ 2 < (D : ℝ) := by nlinarith
      exact_mod_cast h
    · have h : (D : ℝ) < (upper : ℝ) ^ 2 := by nlinarith
      exact_mod_cast h

theorem reversed_enclosure_refused {D lower upper : ℚ} (h : upper ≤ lower) :
    ¬ EnclosureAccepted D lower upper := by
  intro ha
  exact (not_lt_of_ge h) ha.1

theorem nonpositive_lower_refused {D lower upper : ℚ} (h : lower ≤ 0) :
    ¬ EnclosureAccepted D lower upper := by
  intro ha
  exact (not_lt_of_ge h) ha.2.1

theorem rational_square_refused {D : ℚ} (h : ∃ r : ℚ, r ^ 2 = D) :
    ¬ Nonsquare D := by
  obtain ⟨r, hr⟩ := h
  intro hD
  exact hD r hr

theorem zero_norm_refused (D : ℚ) : norm D (0, 0) = 0 := by
  simp [norm]

/-- The native min/max enclosure contains the evaluated linear expression,
including negative coefficient, zero coefficient and rational collapse. -/
theorem linear_enclosure_sound {D lower upper : ℚ} {s : ℝ}
    (ha : EnclosureAccepted D lower upper) (hs : 0 < s)
    (hsq : s ^ 2 = (D : ℝ)) (u v : ℚ) :
    (min (u + v * lower) (u + v * upper) : ℚ) ≤ evaluate s (u, v) ∧
      evaluate s (u, v) ≤ (max (u + v * lower) (u + v * upper) : ℚ) := by
  obtain ⟨hl, hu⟩ := enclosure_acceptance_sound ha hs hsq
  rw [evaluate_formula]
  by_cases hv : 0 ≤ v
  · have horder : u + v * lower ≤ u + v * upper := by
      nlinarith [ha.1]
    rw [min_eq_left horder, max_eq_right horder]
    have hvR : (0 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    push_cast
    constructor <;> nlinarith
  · have hv' : v ≤ 0 := le_of_lt (lt_of_not_ge hv)
    have horder : u + v * upper ≤ u + v * lower := by
      nlinarith [ha.1]
    rw [min_eq_right horder, max_eq_left horder]
    have hvR : (v : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hv'
    push_cast
    constructor <;> nlinarith

#print axioms positive_root_exists
#print axioms positive_root_unique
#print axioms same_radicand_same_selected_root
#print axioms distinct_radicands_distinct_selected_roots
#print axioms enclosure_acceptance_sound
#print axioms enclosure_acceptance_iff
#print axioms reversed_enclosure_refused
#print axioms nonpositive_lower_refused
#print axioms rational_square_refused
#print axioms zero_norm_refused
#print axioms linear_enclosure_sound
end Holonics.Objects.Ratio.SelectedQuadratic
