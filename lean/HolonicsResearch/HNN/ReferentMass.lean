import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# A referent's mass counts its returns, and its region is the running mean

The record `research/records/2026-10-26_A_REFERENT_IS_DENSE_BY_THE_LOOPS_THAT_CLOSE_THROUGH_IT_AND_SEVEN_IN_TEN_RUN_THROUGH_A_PRONOUN.md`
(§3.2, atlas `receiver.referent-mass`) reads a referent's mass from the reading law
`1/h′ = 1/h + 1` (`spectro.reading-mass`): each identified return adds one to the inverse reading
weight, and the region moves toward the return by its share `1/(M + 1)`, `M = 1/h`. #410 owes the
iterated law; this file proves it in any field of characteristic zero, so it is exact over `ℚ`.

[proved-standard; formal-checked] What is proved.

1. **The mass counts the returns** (`inverse_mass_after`, `mass_from_opening`): if every return
   adds one to `1/h`, then after `k` returns `1/h_k = 1/h₀ + k`; from an opening of mass `1`,
   `1/h_k = k + 1`, so the next return's share is `1/(k + 1)`.
2. **The region is the running mean of its returns** (`running_mean`): the update
   `w_(k+1) = w_k + (y_(k+1) − w_k)/(k + 1)` gives `w_k = (1/k) Σ_(1≤j≤k) y_j` for every `k ≥ 1`,
   whatever the opening `w₀`.
3. **The pull of a dense region** (`pull_toward_region`): the step moves the region by
   `M/(M + 1)` of the way it does not move toward the return, `w′ − y = (M/(M + 1))(w − y)` with
   `M = k`, so a heavy region bends the next crossing toward itself.

Consumers: the atlas rows `receiver.referent-mass` and `spectro.reading-mass`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ReferentMass

variable {K : Type*} [Field K] [CharZero K]

/-- [proved-standard; formal-checked] **The mass counts the returns:** `1/h_k = 1/h₀ + k`. -/
theorem inverse_mass_after (h : ℕ → K) (hstep : ∀ k, (h (k + 1))⁻¹ = (h k)⁻¹ + 1) (k : ℕ) :
    (h k)⁻¹ = (h 0)⁻¹ + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hstep, ih]
    push_cast
    ring

/-- [proved-standard; formal-checked] From an opening of mass `1`, `1/h_k = k + 1`. -/
theorem mass_from_opening (h : ℕ → K) (hstep : ∀ k, (h (k + 1))⁻¹ = (h k)⁻¹ + 1)
    (h0 : h 0 = 1) (k : ℕ) : (h k)⁻¹ = k + 1 := by
  rw [inverse_mass_after h hstep, h0, inv_one]
  ring

/-- [proved-standard; formal-checked] **The region is the running mean of its returns.** -/
theorem running_mean (w y : ℕ → K)
    (hstep : ∀ k, w (k + 1) = w k + (y (k + 1) - w k) / (k + 1)) (k : ℕ) :
    w (k + 1) = (∑ j ∈ Finset.Icc 1 (k + 1), y j) / (k + 1) := by
  induction k with
  | zero =>
    rw [hstep]
    simp
  | succ k ih =>
    rw [hstep, ih, Finset.sum_Icc_succ_top (show 1 ≤ k + 1 + 1 by omega)]
    have hk1 : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk2 : ((k : K) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
    push_cast
    field_simp
    ring

/-- [proved-standard; formal-checked] **The pull of a dense region:** after the step with share
`1/(M + 1)`, the region's offset from the return is `M/(M + 1)` of its offset before. -/
theorem pull_toward_region (w y M : K) (hM : M + 1 ≠ 0) :
    (w + (y - w) / (M + 1)) - y = (M / (M + 1)) * (w - y) := by
  field_simp
  ring

end Holonics.HNN.ReferentMass
