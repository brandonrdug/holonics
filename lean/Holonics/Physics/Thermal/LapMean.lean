import Holonics.Physics.Thermal.LinearDiffusion

/-!
# A walk read at its laps' means: the weights of the difference of two successive lap means

[definition] Issue #410; atlas `deposition.lap-mean-quarter-floor`. A walk `X t = Σ_{u<t} ε u` is
read at the mean of each lap of `n` steps, `M k = (1/n) Σ_{j<n} X (k n + j + 1)`, the reading
`holonics::hnn::tower::field::MaterialMean` takes of a deposit's material (atlas
`tower.field-lap-mean`).

[proved-standard] The chart, cited and not formalized here (the reindexing is owed in #410).
- The difference of two successive lap means is a weighted sum of the increments of the two laps
  it spans: `n (M (k+1) − M k) = Σ_{i<n} i · ε (k n + i) + Σ_{i<n} (n − i) · ε ((k+1) n + i)`.
- For increments that are uncorrelated and of one variance `v`, that difference has the variance
  `v (Σ_{i<n} i² + Σ_{i<n} (i+1)²)/n²`, and two successive differences, which share one lap's
  increments at the weights `n − i` and `i`, have the covariance `v Σ_{i<n} i (n − i)/n²`.
- With `σ² = n v` the walk's variance a lap, these are `σ² (2n² + 1)/(3n²)` and
  `σ² (n² − 1)/(6n²)`: two thirds and one sixth of `σ²` for a lap of many steps.

[proved-derived; formal-checked] What is proved, on the weights.

1. **The shared weight** (`six_mul_shared`): `6 Σ_{i<n} i (n − i) = n (n − 1)(n + 1)`.
2. **The own weight** (`six_mul_own`): `6 (Σ_{i<n} i² + Σ_{i<n} (i+1)²) = n (4n² + 2)`.
3. **Own is four times shared and `n` more** (`own_eq_four_mul_shared_add`). So the lap cosine of
   a free walk between lap means, shared over own, `(n² − 1)/(4n² + 2)`, stands under one quarter
   at every `n` (`four_mul_shared_lt_own`), is zero at `n = 1` (the lap's end alone), and tends
   to one quarter. A lap cosine read on lap means has that floor where a lap cosine read on lap
   ends has the floor zero.
4. **The cosine is the steady share and a quarter of the rest** (`cosine_eq_share_add_quarter`):
   with a travel `d` a lap that repeats beside a free walk of variance `σ²` a lap, in the limit
   of many steps, two successive differences of lap means share `a + b/6` and each holds
   `a + 2b/3` (`a = d²`, `b = σ²`). With `s = a/(a + 2b/3)`, the steady share of the squared
   travel between lap means, the cosine is `c = s + (1 − s)/4`, so `s = (4c − 1)/3`.

Rust owner: none; the cosines are read from saved lap means on the host
(`tools/state_travel.py scale`, `tools/part_rates.py means`).
-/

namespace Holonics.Physics.Thermal.LapMean

open Finset
open scoped BigOperators

/-- [proved-standard; formal-checked] `6 Σ_{m<n} m (k − m) = n (n − 1)(3k − 2n + 1)`. -/
theorem six_mul_sum_mul_sub (n : ℕ) (k : ℤ) :
    6 * ∑ m ∈ range n, (m : ℤ) * (k - m) = n * (n - 1) * (3 * k - 2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih

/-- [proved-standard; formal-checked] `6 Σ_{m<n} m² = n (n − 1)(2n − 1)`. -/
theorem six_mul_sum_sq (n : ℕ) :
    (6 : ℤ) * ∑ m ∈ range n, (m : ℤ) ^ 2
      = (n : ℤ) * ((n : ℤ) - 1) * (2 * (n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih

/-- [proved-standard; formal-checked] `6 Σ_{m<n} (m + 1)² = n (n + 1)(2n + 1)`. -/
theorem six_mul_sum_succ_sq (n : ℕ) :
    (6 : ℤ) * ∑ m ∈ range n, ((m : ℤ) + 1) ^ 2
      = (n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih

/-- [proved-derived; formal-checked] **The shared weight** of two successive differences of lap
means, on the one lap both span: `6 Σ_{i<n} i (n − i) = n (n − 1)(n + 1)`. -/
theorem six_mul_shared (n : ℕ) :
    6 * ∑ m ∈ range n, (m : ℤ) * ((n : ℤ) - m) = n * (n - 1) * (n + 1) := by
  linear_combination six_mul_sum_mul_sub n (n : ℤ)

/-- [proved-derived; formal-checked] **The own weight** of a difference of two successive lap
means, over the two laps it spans: `6 (Σ_{i<n} i² + Σ_{i<n} (i + 1)²) = n (4n² + 2)`. -/
theorem six_mul_own (n : ℕ) :
    (6 : ℤ) * (∑ m ∈ range n, (m : ℤ) ^ 2 + ∑ m ∈ range n, ((m : ℤ) + 1) ^ 2)
      = (n : ℤ) * (4 * (n : ℤ) ^ 2 + 2) := by
  linear_combination six_mul_sum_sq n + six_mul_sum_succ_sq n

/-- [proved-derived; formal-checked] **Own is four times shared and `n` more.** The lap cosine of
a free walk's lap means, shared over own, is `(n² − 1)/(4n² + 2)`. -/
theorem own_eq_four_mul_shared_add (n : ℕ) :
    ∑ m ∈ range n, (m : ℤ) ^ 2 + ∑ m ∈ range n, ((m : ℤ) + 1) ^ 2
      = (4 : ℤ) * ∑ m ∈ range n, (m : ℤ) * ((n : ℤ) - m) + (n : ℤ) := by
  have h : (6 : ℤ) * (∑ m ∈ range n, (m : ℤ) ^ 2 + ∑ m ∈ range n, ((m : ℤ) + 1) ^ 2)
      = 6 * ((4 : ℤ) * ∑ m ∈ range n, (m : ℤ) * ((n : ℤ) - m) + (n : ℤ)) := by
    linear_combination six_mul_own n - 4 * six_mul_shared n
  exact mul_left_cancel₀ (by norm_num) h

/-- [proved-derived; formal-checked] **The quarter floor:** between lap means a free walk's lap
cosine is under one quarter at every lap length. -/
theorem four_mul_shared_lt_own (n : ℕ) (hn : 0 < n) :
    (4 : ℤ) * ∑ m ∈ range n, (m : ℤ) * ((n : ℤ) - m)
      < ∑ m ∈ range n, (m : ℤ) ^ 2 + ∑ m ∈ range n, ((m : ℤ) + 1) ^ 2 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h := own_eq_four_mul_shared_add n
  linarith

/-- [proved-derived; formal-checked] **A lap-mean cosine is the steady share and a quarter of the
rest.** With `a` the square of a lap's repeating travel and `b` the free walk's variance a lap,
two successive differences of lap means share `a + b/6` and each holds `a + 2b/3`; the steady
share `s` and the cosine `c` are their ratios to `a + 2b/3`. -/
theorem cosine_eq_share_add_quarter (a b s c : ℚ) (h : a + 2 * b / 3 ≠ 0)
    (hs : s * (a + 2 * b / 3) = a) (hc : c * (a + 2 * b / 3) = a + b / 6) :
    c = s + (1 - s) / 4 := by
  have h0 : (c - (s + (1 - s) / 4)) * (a + 2 * b / 3) = 0 := by
    linear_combination hc - (3 / 4 : ℚ) * hs
  rcases mul_eq_zero.mp h0 with h1 | h1
  · linarith
  · exact absurd h1 h

end Holonics.Physics.Thermal.LapMean
