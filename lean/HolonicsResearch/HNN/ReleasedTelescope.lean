import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The released ratio's telescope: the receiving tree's widths are set by its grain

The record `research/records/2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ.md`
(§7) reads a node of the receiving tree (`compression::landmark::context`) as a mixture of its own
face `e` and its children's face `k` at a ratio `β`, `q = (β e + k)/(β + 1)`, whose step on a reading
is `β' = β e/k`. Because `1 + β' = (1 + β) q/k`, the code of the mixture telescopes for any release
`β_(t+1) = R(β'_t)` of the ratio, with no ideal mixture to track. #410 owes that telescope and the
cost of the clamp; this file proves both.

[proved-standard; formal-checked] What is proved.

1. **One cell's code** (`neg_log_mixture`, `neg_log_mixture_mirror`):
   `−ln q = −ln k + ln(1 + β) − ln(1 + β')` and `−ln q = −ln e + ln(1 + 1/β) − ln(1 + 1/β')`.
2. **The telescope** (`released_telescope`, `released_telescope_mirror`): for any positive ratios
   `β_t`, `Σ_(t<n) −ln q_t = Σ −ln k_t + ln(1 + β_0) − ln(1 + β_n) + Σ_t [ln(1 + β_(t+1)) − ln(1 + β'_t)]`,
   and its mirror in `e`. The release enters only through `β_(t+1)`.
3. **The clamp's cost** (`clamp_cases`, `release_cost`): releasing a positive step into
   `[2^(−K), 2^K]` costs at most `ln(1 + 2^(−K))` on each line, and nothing on one of them: at the
   upper bound nothing against `k`, at the lower bound nothing against `e`, inside the band nothing.
4. **The node tracks either face** (`released_code_le`, `released_code_le_mirror`): under the clamp,
   `Σ −ln q ≤ Σ −ln k + ln(1 + β_0) − ln(1 + β_n) + n ln(1 + 2^(−K))`, and the same with `e` and
   `1/β`. The passage enters once, through the count of cells, never through the width of the ratio.

The computational object is the helical pair interaction: the node's ratio is the undivided pair of
its two faces' readings, and the release is the carried-release law at that pair. Of the winding
guide's six general objects this touches faces and placement (the two faces and their mixture) and
the tower thread (the tree's node); the helix, the pair, the cell holonomy and the tube stay
attached.

Consumers: `compression::landmark::context` (the node's ratio and its release) and the record's §7.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ReleasedTelescope

open Real Finset

/-- [definition] The node's mixture of its own face `e` and its children's face `k` at ratio `β`. -/
noncomputable def mixture (β e k : ℝ) : ℝ := (β * e + k) / (β + 1)

/-- [definition] The ratio's step on a reading, `β' = β e/k`. -/
noncomputable def step (β e k : ℝ) : ℝ := β * e / k

/-- [definition] The release of a ratio into `[2^(−K), 2^K]`. -/
noncomputable def clamp (K : ℕ) (x : ℝ) : ℝ := max ((2 : ℝ) ^ K)⁻¹ (min x ((2 : ℝ) ^ K))

section Cell

variable {β e k : ℝ}

theorem step_pos (hβ : 0 < β) (he : 0 < e) (hk : 0 < k) : 0 < step β e k :=
  div_pos (mul_pos hβ he) hk

theorem mixture_pos (hβ : 0 < β) (he : 0 < e) (hk : 0 < k) : 0 < mixture β e k :=
  div_pos (add_pos (mul_pos hβ he) hk) (by linarith)

/-- [proved-standard; formal-checked] **One cell's code against the children's face:**
`−ln q = −ln k + ln(1 + β) − ln(1 + β')`. -/
theorem neg_log_mixture (hβ : 0 < β) (he : 0 < e) (hk : 0 < k) :
    -log (mixture β e k) = -log k + log (1 + β) - log (1 + step β e k) := by
  have hβ1 : (1 + β) ≠ 0 := by linarith
  have hβ1' : (β + 1) ≠ 0 := by linarith
  have hk0 : k ≠ 0 := hk.ne'
  have hs : 0 < 1 + step β e k := by linarith [step_pos hβ he hk]
  have hq : mixture β e k = k * (1 + step β e k) / (1 + β) := by
    unfold mixture step
    field_simp
    ring
  rw [hq, log_div (mul_pos hk hs).ne' hβ1, log_mul hk0 hs.ne']
  ring

/-- [proved-standard; formal-checked] **One cell's code against the node's own face:**
`−ln q = −ln e + ln(1 + 1/β) − ln(1 + 1/β')`. -/
theorem neg_log_mixture_mirror (hβ : 0 < β) (he : 0 < e) (hk : 0 < k) :
    -log (mixture β e k) = -log e + log (1 + β⁻¹) - log (1 + (step β e k)⁻¹) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have he0 : e ≠ 0 := he.ne'
  have hk0 : k ≠ 0 := hk.ne'
  have hβ1 : 0 < 1 + β⁻¹ := by have := inv_pos.mpr hβ; linarith
  have hs : 0 < 1 + (step β e k)⁻¹ := by have := inv_pos.mpr (step_pos hβ he hk); linarith
  have hq : mixture β e k = e * (1 + (step β e k)⁻¹) / (1 + β⁻¹) := by
    have hβ1' : β + 1 ≠ 0 := by linarith
    unfold mixture step
    field_simp
  rw [hq, log_div (mul_pos he hs).ne' hβ1.ne', log_mul he0 hs.ne']
  ring

end Cell

section Passage

variable (β e k : ℕ → ℝ)

/-- [proved-standard; formal-checked] **The released ratio's telescope:** for any positive ratios,
`Σ −ln q_t = Σ −ln k_t + ln(1 + β_0) − ln(1 + β_n) + Σ [ln(1 + β_(t+1)) − ln(1 + β'_t)]`. -/
theorem released_telescope (hβ : ∀ t, 0 < β t) (he : ∀ t, 0 < e t) (hk : ∀ t, 0 < k t) (n : ℕ) :
    ∑ t ∈ range n, -log (mixture (β t) (e t) (k t)) =
      ∑ t ∈ range n, -log (k t) + log (1 + β 0) - log (1 + β n) +
        ∑ t ∈ range n, (log (1 + β (t + 1)) - log (1 + step (β t) (e t) (k t))) := by
  rw [Finset.sum_congr rfl fun t _ => neg_log_mixture (hβ t) (he t) (hk t)]
  have htel := Finset.sum_range_sub' (fun t => log (1 + β t)) n
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at htel ⊢
  linarith

/-- [proved-standard; formal-checked] **The telescope's mirror in the node's own face.** -/
theorem released_telescope_mirror (hβ : ∀ t, 0 < β t) (he : ∀ t, 0 < e t) (hk : ∀ t, 0 < k t)
    (n : ℕ) :
    ∑ t ∈ range n, -log (mixture (β t) (e t) (k t)) =
      ∑ t ∈ range n, -log (e t) + log (1 + (β 0)⁻¹) - log (1 + (β n)⁻¹) +
        ∑ t ∈ range n,
          (log (1 + (β (t + 1))⁻¹) - log (1 + (step (β t) (e t) (k t))⁻¹)) := by
  rw [Finset.sum_congr rfl fun t _ => neg_log_mixture_mirror (hβ t) (he t) (hk t)]
  have htel := Finset.sum_range_sub' (fun t => log (1 + (β t)⁻¹)) n
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at htel ⊢
  linarith

end Passage

section Release

/-- [proved-standard; formal-checked] The clamp leaves a ratio in the band and moves one outside it
to the nearer bound. -/
theorem clamp_cases (K : ℕ) (x : ℝ) :
    (x < ((2 : ℝ) ^ K)⁻¹ ∧ clamp K x = ((2 : ℝ) ^ K)⁻¹) ∨
      (((2 : ℝ) ^ K)⁻¹ ≤ x ∧ x ≤ (2 : ℝ) ^ K ∧ clamp K x = x) ∨
      ((2 : ℝ) ^ K < x ∧ clamp K x = (2 : ℝ) ^ K) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hε : ((2 : ℝ) ^ K)⁻¹ ≤ (2 : ℝ) ^ K := (inv_le_one_of_one_le₀ h1).trans h1
  rcases lt_or_ge x ((2 : ℝ) ^ K)⁻¹ with h | h
  · refine Or.inl ⟨h, ?_⟩
    unfold clamp
    rw [min_eq_left (by linarith), max_eq_left h.le]
  · rcases le_or_gt x ((2 : ℝ) ^ K) with h' | h'
    · refine Or.inr (Or.inl ⟨h, h', ?_⟩)
      unfold clamp
      rw [min_eq_left h', max_eq_right h]
    · refine Or.inr (Or.inr ⟨h', ?_⟩)
      unfold clamp
      rw [min_eq_right h'.le, max_eq_right hε]

/-- [proved-standard; formal-checked] **The clamp's cost:** releasing a positive step into
`[2^(−K), 2^K]` costs at most `ln(1 + 2^(−K))` against either face, and nothing against one of
them. -/
theorem release_cost (K : ℕ) {x : ℝ} (hx : 0 < x) :
    log (1 + clamp K x) - log (1 + x) ≤ log (1 + ((2 : ℝ) ^ K)⁻¹) ∧
      log (1 + (clamp K x)⁻¹) - log (1 + x⁻¹) ≤ log (1 + ((2 : ℝ) ^ K)⁻¹) ∧
      (log (1 + clamp K x) - log (1 + x) ≤ 0 ∨ log (1 + (clamp K x)⁻¹) - log (1 + x⁻¹) ≤ 0) := by
  have hε : (0 : ℝ) < ((2 : ℝ) ^ K)⁻¹ := by positivity
  have hM : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hcost : 0 ≤ log (1 + ((2 : ℝ) ^ K)⁻¹) := log_nonneg (by linarith)
  have hx0 : 0 ≤ log (1 + x) := log_nonneg (by linarith)
  have hxi : 0 ≤ log (1 + x⁻¹) := log_nonneg (by linarith [inv_pos.mpr hx])
  rcases clamp_cases K x with ⟨h, hc⟩ | ⟨-, -, hc⟩ | ⟨h, hc⟩
  · -- the lower bound: nothing against `e`
    rw [hc, inv_inv]
    have hinv : (2 : ℝ) ^ K < x⁻¹ := by
      have h' := (inv_lt_inv₀ hε hx).mpr h
      rwa [inv_inv] at h'
    have he : log (1 + (2 : ℝ) ^ K) ≤ log (1 + x⁻¹) := log_le_log (by linarith) (by linarith)
    refine ⟨by linarith, by linarith, Or.inr (by linarith)⟩
  · -- inside the band: nothing against either
    rw [hc, sub_self, sub_self]
    exact ⟨hcost, hcost, Or.inl le_rfl⟩
  · -- the upper bound: nothing against `k`
    rw [hc]
    have hk : log (1 + (2 : ℝ) ^ K) ≤ log (1 + x) := log_le_log (by linarith) (by linarith)
    refine ⟨by linarith, by linarith, Or.inl (by linarith)⟩

/-- [proved-standard; formal-checked] **The node tracks its children's face:** under the clamp,
`Σ −ln q ≤ Σ −ln k + ln(1 + β_0) − ln(1 + β_n) + n ln(1 + 2^(−K))`. -/
theorem released_code_le (K : ℕ) (β e k : ℕ → ℝ) (hβ : ∀ t, 0 < β t) (he : ∀ t, 0 < e t)
    (hk : ∀ t, 0 < k t) (hR : ∀ t, β (t + 1) = clamp K (step (β t) (e t) (k t))) (n : ℕ) :
    ∑ t ∈ range n, -log (mixture (β t) (e t) (k t)) ≤
      ∑ t ∈ range n, -log (k t) + log (1 + β 0) - log (1 + β n) +
        n * log (1 + ((2 : ℝ) ^ K)⁻¹) := by
  rw [released_telescope β e k hβ he hk n]
  have h : ∑ t ∈ range n, (log (1 + β (t + 1)) - log (1 + step (β t) (e t) (k t))) ≤
      ∑ _t ∈ range n, log (1 + ((2 : ℝ) ^ K)⁻¹) :=
    Finset.sum_le_sum fun t _ => by
      rw [hR t]
      exact (release_cost K (step_pos (hβ t) (he t) (hk t))).1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith

/-- [proved-standard; formal-checked] **The node tracks its own face:** under the clamp,
`Σ −ln q ≤ Σ −ln e + ln(1 + 1/β_0) − ln(1 + 1/β_n) + n ln(1 + 2^(−K))`. -/
theorem released_code_le_mirror (K : ℕ) (β e k : ℕ → ℝ) (hβ : ∀ t, 0 < β t)
    (he : ∀ t, 0 < e t) (hk : ∀ t, 0 < k t)
    (hR : ∀ t, β (t + 1) = clamp K (step (β t) (e t) (k t))) (n : ℕ) :
    ∑ t ∈ range n, -log (mixture (β t) (e t) (k t)) ≤
      ∑ t ∈ range n, -log (e t) + log (1 + (β 0)⁻¹) - log (1 + (β n)⁻¹) +
        n * log (1 + ((2 : ℝ) ^ K)⁻¹) := by
  rw [released_telescope_mirror β e k hβ he hk n]
  have h : ∑ t ∈ range n,
        (log (1 + (β (t + 1))⁻¹) - log (1 + (step (β t) (e t) (k t))⁻¹)) ≤
      ∑ _t ∈ range n, log (1 + ((2 : ℝ) ^ K)⁻¹) :=
    Finset.sum_le_sum fun t _ => by
      rw [hR t]
      exact (release_cost K (step_pos (hβ t) (he t) (hk t))).2.1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith

end Release

end Holonics.HNN.ReleasedTelescope
