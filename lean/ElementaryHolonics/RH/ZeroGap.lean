import Mathlib

/-!
# A height between the zeros

Given finitely many real numbers (the imaginary parts of the zeros in a window), every unit
interval contains a height whose distance from each of them is at least `1 / (2 (N + 1))`, where
`N` is their number.  The `N + 2` candidates `a + k / (N + 1)` are spaced `1 / (N + 1)` apart, so
each real number blocks at most one candidate, and at least two candidates remain free.

This is the height selection for the horizontal edges of the explicit-formula rectangle.
-/

open Finset Set

namespace Soma.Holonics.RH.ZeroGap

/-- Two candidates within `1 / (2 (N + 1))` of the same point coincide. -/
theorem cand_eq_of_close (a : ℝ) (N : ℕ) (p : ℝ) (j k : ℕ)
    (hj : |a + j / (N + 1 : ℝ) - p| < 1 / (2 * (N + 1)))
    (hk : |a + k / (N + 1 : ℝ) - p| < 1 / (2 * (N + 1))) : j = k := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hdiff : |(j : ℝ) - k| < 1 := by
    have h1 : |a + j / (N + 1 : ℝ) - p - (a + k / (N + 1 : ℝ) - p)| < 1 / (N + 1) := by
      calc |a + j / (N + 1 : ℝ) - p - (a + k / (N + 1 : ℝ) - p)|
          ≤ |a + j / (N + 1 : ℝ) - p| + |a + k / (N + 1 : ℝ) - p| := abs_sub _ _
        _ < 1 / (2 * (N + 1)) + 1 / (2 * (N + 1)) := add_lt_add hj hk
        _ = 1 / (N + 1) := by field_simp; norm_num
    have h2 : a + j / (N + 1 : ℝ) - p - (a + k / (N + 1 : ℝ) - p) = ((j : ℝ) - k) / (N + 1) := by
      ring
    rw [h2, abs_div, abs_of_pos hN, div_lt_div_iff_of_pos_right hN] at h1
    exact h1
  rcases lt_trichotomy j k with h | h | h
  · exfalso
    have : (j : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt h
    have := (abs_lt.mp hdiff).1
    linarith
  · exact h
  · exfalso
    have : (k : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    have := (abs_lt.mp hdiff).2
    linarith

/-- **Height selection.**  Every unit interval contains a point at distance at least
`1 / (2 (N + 1))` from each of `N` given real numbers. -/
theorem exists_gap (S : Finset ℝ) (a : ℝ) :
    ∃ T ∈ Icc a (a + 1), ∀ p ∈ S, 1 / (2 * (S.card + 1 : ℝ)) ≤ |T - p| := by
  classical
  set N := S.card with hN
  let cand : ℕ → ℝ := fun k => a + k / (N + 1 : ℝ)
  let ε : ℝ := 1 / (2 * (N + 1 : ℝ))
  let blocker : ℝ → ℕ := fun p => if h : ∃ k, |cand k - p| < ε then h.choose else 0
  have hcard : (S.image blocker).card < (Finset.range (N + 2)).card := by
    calc (S.image blocker).card ≤ S.card := Finset.card_image_le
      _ < N + 2 := by omega
      _ = (Finset.range (N + 2)).card := (Finset.card_range _).symm
  obtain ⟨k, hk, hkb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hk' : k < N + 2 := Finset.mem_range.mp hk
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  refine ⟨cand k, ⟨?_, ?_⟩, ?_⟩
  · show a ≤ a + k / (N + 1 : ℝ)
    have : (0 : ℝ) ≤ k / (N + 1 : ℝ) := by positivity
    linarith
  · show a + k / (N + 1 : ℝ) ≤ a + 1
    have : (k : ℝ) / (N + 1 : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      exact_mod_cast (by omega : k ≤ N + 1)
    linarith
  · intro p hp
    by_contra hlt
    push Not at hlt
    apply hkb
    rw [Finset.mem_image]
    refine ⟨p, hp, ?_⟩
    have hex : ∃ k, |cand k - p| < ε := ⟨k, hlt⟩
    show (if h : ∃ k, |cand k - p| < ε then h.choose else 0) = k
    rw [dif_pos hex]
    exact cand_eq_of_close a N p _ _ hex.choose_spec hlt

end Soma.Holonics.RH.ZeroGap
