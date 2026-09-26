import Holonics.HNN.LandmarkTree

/-!
# HNN.LandmarkCarrier: the tree's carriers rebase past their width

[definition; agent-inferred] Campaign 2 of rebuild step 4 (`docs/plans/THE_REBUILD.md`, Lean item
14 of table (b); #73), from Sol's review of the campaign (§4). The computational object is the
helical pair interaction; this owner is the fixed-width carrier of the landmark tree's mixture
ratio `β` (`HNN/LandmarkTree`, section 6′). Of the winding guide's six general objects it touches
the **helix** (a carrier's common power of two is a carry, its kept part the phase within the
octave) and **faces and placement** (the released ratio's interval, carried to the faces it
reaches). No holonomy is claimed.

A campaign 1 tree was refused past 87,382 cells because the β step's carrier `(N, D)` could pass
`u128`: a carrier-width failure, not a stopping rule (Sol's review §4). Before a product can
overflow, the carrier rebases by a common power of two:

```text
rebase     N = 2^e N̂ + r_N ,  D = 2^e D̂ + r_D ,  0 ≤ r < 2^e        exact while r_N, r_D are carried
released   N̂/(D̂ + 1) ≤ N/D ≤ (N̂ + 1)/D̂ ;   r_N = 0:  N/D ≤ N̂/D̂ < (N/D)(1 + 1/D̂)
propagate  β ∈ [β̌, β̌(1 + δ)]  ⇒  β k/x ∈ [β̌ k/x, β̌ k/x (1 + δ)] ,  (β k + q)/(1 + β) within (1 + δ)
total      Σ_t log₂((1 + δ_t)(1 − r_t)) ≤ n (2^(3−W) + 2^(2−R))  with δ_t ≤ 2^(1−R), r_t < 2^(1−W)
width      a < 2^(w_a), b < 2^(w_b):  w_a + w_b ≤ W ⇒ a b < 2^W ;  otherwise a ⌊b/2^e⌋ < 2^W at e = w_a + w_b − W
```

[proved-derived; formal-checked] What is proved.

1. **`rebase_decode`.** A carrier coordinate is its kept part times `2^e` plus its remainder below
   `2^e`, and the ratio of the two decoded coordinates is the carrier's ratio exactly: nothing is
   lost while the remainders are carried.
2. **`rebase_ratio_enclosed`.** When the remainders are released, the ratio lies in
   `[N̂/(D̂ + 1), (N̂ + 1)/D̂]`; when the numerator's remainder is zero (the Rust step scales the
   numerator past `e`, so only `r_D` is released) the carried `N̂/D̂` lies in `[v, v (1 + 1/D̂))` of
   the exact ratio `v`, and its logarithmic width is below `1/D̂`.
3. **`rebase_step_enclosed`.** A released enclosure of `β` propagates through every later step: the
   likelihood-ratio step `β k/x` scales it, and the path mixture `(β k + q)/(1 + β)` (a node's face,
   the join's, the receiver's mixture) moves by at most the enclosure's factor
   (`LandmarkTree.mix_ratio_bound` at `ρ_q = 1`), lying between the mixtures of its endpoints.
4. **`rebase_log_residual_sum`.** Over a passage whose steps release carrier widths
   `δ_t ≤ 2^(1−R)` and keep mantissas with residuals `r_t < 2^(1−W)`
   (`LandmarkTree.rebase_log_residual`), the total `|log₂ ∏_t (1 + δ_t)(1 − r_t)|` is at most
   `n (2^(3−W) + 2^(2−R))`: the rebases add, never compound.
5. **`width_or_rebase_total`.** A product of operands of `w_a` and `w_b` bits either fits the
   carrier's `W` bits exactly, or fits after the second operand rebases by `e = w_a + w_b − W`, its
   released relative width below `1/⌊b/2^e⌋ ≤ 2^(1 + e − w_b)` for a `w_b`-bit `b`; over `n` such
   steps with kept parts of at least `R` bits the released widths sum to at most `n 2^(1−R)`.

The Rust consumer is `crates/holonics/src/hnn/landmark.rs`: `Beta::step` (the carrier's rebase at
`R = 126 − W` bits and its release), the node's and the join's certificates (the release's
`⌈2^C/D̂⌉` added to their drift and excess), `Widths::rebase` and `Landmarks::face_rule`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LandmarkCarrier

open Holonics.HNN.LandmarkTree (rebase_log_residual mix_ratio_bound)

/-- [definition] **The kept part** of a carrier coordinate rebased by `2^e`. -/
def kept (e N : ℕ) : ℕ := N / 2 ^ e

/-- [definition] **The remainder** of a carrier coordinate rebased by `2^e`, below `2^e`. -/
def remainder (e N : ℕ) : ℕ := N % 2 ^ e

/-- [proved-derived; formal-checked] **`rebase_decode`: the rebased carrier decodes exactly.**
`N = 2^e N̂ + r_N` with `0 ≤ r_N < 2^e`, likewise `D`, and the decoded ratio is the carrier's
ratio: exact while the remainders are carried. -/
theorem rebase_decode (e N D : ℕ) :
    N = 2 ^ e * kept e N + remainder e N ∧ remainder e N < 2 ^ e ∧
      D = 2 ^ e * kept e D + remainder e D ∧ remainder e D < 2 ^ e ∧
      (N : ℚ) / D = ((2 ^ e * kept e N + remainder e N : ℕ) : ℚ) /
        ((2 ^ e * kept e D + remainder e D : ℕ) : ℚ) := by
  have hN := (Nat.div_add_mod N (2 ^ e)).symm
  have hD' := (Nat.div_add_mod D (2 ^ e)).symm
  have hpos : 0 < 2 ^ e := Nat.two_pow_pos e
  refine ⟨hN, Nat.mod_lt _ hpos, hD', Nat.mod_lt _ hpos, ?_⟩
  simp only [kept, remainder]
  rw [← hN, ← hD']

/-- [proved-derived; formal-checked] **`rebase_ratio_enclosed`: a released remainder's ratio
interval.** For a positive kept denominator `D̂`:
* the ratio lies in `[N̂/(D̂ + 1), (N̂ + 1)/D̂]`;
* when the numerator's remainder is zero, the carried `N̂/D̂` lies in `[v, v (1 + 1/D̂))` of the
  exact ratio `v = N/D`, and its logarithmic width is below `1/D̂`. -/
theorem rebase_ratio_enclosed (e N D : ℕ) (hk : 0 < kept e D) :
    ((kept e N : ℚ) / (kept e D + 1) ≤ (N : ℚ) / D ∧
        (N : ℚ) / D ≤ ((kept e N : ℚ) + 1) / kept e D) ∧
      (remainder e N = 0 →
        (N : ℚ) / D ≤ (kept e N : ℚ) / kept e D ∧
          (kept e N : ℚ) / kept e D ≤ (N : ℚ) / D * (1 + 1 / kept e D) ∧
          Real.log (((kept e D : ℝ) + 1) / kept e D) < 1 / kept e D) := by
  have hpos : (0 : ℚ) < 2 ^ e := by positivity
  have hN := (Nat.div_add_mod N (2 ^ e)).symm
  have hD := (Nat.div_add_mod D (2 ^ e)).symm
  have hrN : N % 2 ^ e < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos e)
  have hrD : D % 2 ^ e < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos e)
  have hk' : (0 : ℚ) < kept e D := by exact_mod_cast hk
  -- The coordinates in ℚ: `N = 2^e N̂ + r_N`, `D = 2^e D̂ + r_D`, `0 ≤ r < 2^e`.
  have eN : (N : ℚ) = 2 ^ e * kept e N + remainder e N := by exact_mod_cast hN
  have eD : (D : ℚ) = 2 ^ e * kept e D + remainder e D := by exact_mod_cast hD
  have rN : (remainder e N : ℚ) < 2 ^ e := by exact_mod_cast hrN
  have rD : (remainder e D : ℚ) < 2 ^ e := by exact_mod_cast hrD
  have rN0 : (0 : ℚ) ≤ remainder e N := by positivity
  have rD0 : (0 : ℚ) ≤ remainder e D := by positivity
  have hD0 : (0 : ℚ) < D := by rw [eD]; positivity
  have hKN : (0 : ℚ) ≤ kept e N := by positivity
  refine ⟨⟨?_, ?_⟩, fun h0 => ⟨?_, ?_, ?_⟩⟩
  · rw [div_le_div_iff₀ (by positivity) hD0, eN, eD]
    nlinarith
  · rw [div_le_div_iff₀ hD0 hk', eN, eD]
    nlinarith
  · have e0 : (remainder e N : ℚ) = 0 := by exact_mod_cast h0
    rw [div_le_div_iff₀ hD0 hk', eN, eD, e0]
    nlinarith
  · have e0 : (remainder e N : ℚ) = 0 := by exact_mod_cast h0
    have hsplit : (N : ℚ) / D * (1 + 1 / kept e D) = (N : ℚ) * (kept e D + 1) / (D * kept e D) := by
      field_simp
    rw [hsplit, div_le_div_iff₀ hk' (by positivity), eN, eD, e0]
    have := mul_le_mul_of_nonneg_left rD.le (mul_nonneg hKN hk'.le)
    nlinarith
  · have hkR : (0 : ℝ) < kept e D := by exact_mod_cast hk
    have e1 : ((kept e D : ℝ) + 1) / kept e D = 1 + 1 / kept e D := by field_simp
    rw [e1]
    have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / kept e D by positivity)
      (by have : (0 : ℝ) < 1 / kept e D := by positivity
          linarith)
    linarith

/-- [proved-derived; formal-checked] **`rebase_step_enclosed`: the released enclosure propagates.**
If `β` lies in `[β̌, β̌ (1 + δ)]` (`β̌ > 0`, `δ ≥ 0`), then for a KT face `k ≥ 0`, a child face
`x > 0` and a face `q > 0`:
* the likelihood-ratio step keeps the enclosure: `β k/x ∈ [β̌ k/x, β̌ k/x (1 + δ)]`;
* the path mixture `(β k + q)/(1 + β)` lies within the factor `1 + δ` of `(β̌ k + q)/(1 + β̌)`
  (`LandmarkTree.mix_ratio_bound` at `ρ_q = 1`);
* and it lies between the mixtures at the enclosure's endpoints (the mixture is monotone in `β`). -/
theorem rebase_step_enclosed {β βl δ k x q : ℚ} (hβl : 0 < βl) (hδ : 0 ≤ δ) (hk : 0 ≤ k)
    (hx : 0 < x) (hq : 0 < q) (h1 : βl ≤ β) (h2 : β ≤ βl * (1 + δ)) :
    (βl * k / x ≤ β * k / x ∧ β * k / x ≤ βl * k / x * (1 + δ)) ∧
      ((β * k + q) / (1 + β) ≤ (1 + δ) * ((βl * k + q) / (1 + βl)) ∧
        (βl * k + q) / (1 + βl) ≤ (1 + δ) * ((β * k + q) / (1 + β))) ∧
      (min ((βl * k + q) / (1 + βl)) ((βl * (1 + δ) * k + q) / (1 + βl * (1 + δ))) ≤
          (β * k + q) / (1 + β) ∧
        (β * k + q) / (1 + β) ≤
          max ((βl * k + q) / (1 + βl)) ((βl * (1 + δ) * k + q) / (1 + βl * (1 + δ)))) := by
  have hβ : 0 < β := lt_of_lt_of_le hβl h1
  have hρ : 1 ≤ 1 + δ := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hk) hx.le
  · rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hx.le
    nlinarith [mul_le_mul_of_nonneg_right h2 hk]
  · have hb := mix_ratio_bound (k := k) (β := βl) (βh := β) (q := q) (qh := q) (ρβ := 1 + δ)
      (ρq := 1) hk hβl hβ hq hq hρ le_rfl (by linarith) (by nlinarith) (by linarith) (by linarith)
    simpa using hb
  · -- The mixture is monotone in `β`: `d/dβ = (k − q)/(1 + β)²`.
    set βh := βl * (1 + δ) with hβh
    have hβh0 : 0 < βh := by positivity
    have key : ∀ {b₁ b₂ : ℚ}, 0 < b₁ → 0 < b₂ → b₁ ≤ b₂ →
        ((b₁ * k + q) / (1 + b₁) ≤ (b₂ * k + q) / (1 + b₂) ∨
          (b₂ * k + q) / (1 + b₂) ≤ (b₁ * k + q) / (1 + b₁)) ∧
        (k ≤ q → (b₂ * k + q) / (1 + b₂) ≤ (b₁ * k + q) / (1 + b₁)) ∧
        (q ≤ k → (b₁ * k + q) / (1 + b₁) ≤ (b₂ * k + q) / (1 + b₂)) := by
      intro b₁ b₂ h₁ h₂ h
      refine ⟨le_total _ _, fun hkq => ?_, fun hqk => ?_⟩
      · rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hkq)]
      · rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hqk)]
    rcases le_total k q with hkq | hqk
    · have a1 := (key hβl hβ h1).2.1 hkq
      have a2 := (key hβ hβh0 h2).2.1 hkq
      exact ⟨min_le_right _ _ |>.trans a2, a1.trans (le_max_left _ _)⟩
    · have a1 := (key hβl hβ h1).2.2 hqk
      have a2 := (key hβ hβh0 h2).2.2 hqk
      exact ⟨min_le_left _ _ |>.trans a1, a2.trans (le_max_right _ _)⟩

/-- [proved-derived; formal-checked] **`rebase_log_residual_sum`: the rebases add over a passage.**
Each step `t < n` keeps a mantissa with residual `r_t ∈ [0, 2^(1−W))` (`W ≥ 2`,
`LandmarkTree.rebase_log_residual`) and releases a carrier width `δ_t ∈ [0, 2^(1−R)]`; then
`|log₂ ∏_(t<n) (1 + δ_t)(1 − r_t)| ≤ n (2^(3−W) + 2^(2−R))`. -/
theorem rebase_log_residual_sum {W R n : ℕ} (hW : 2 ≤ W) (r δ : ℕ → ℝ)
    (hr : ∀ t, 0 ≤ r t ∧ r t < 2 ^ (1 - (W : ℤ))) (hδ : ∀ t, 0 ≤ δ t ∧ δ t ≤ 2 ^ (1 - (R : ℤ))) :
    |Real.logb 2 (∏ t ∈ Finset.range n, (1 + δ t) * (1 - r t))| ≤
      n * (2 ^ (3 - (W : ℤ)) + 2 ^ (2 - (R : ℤ))) := by
  have hW' : (2 : ℝ) ^ (1 - (W : ℤ)) ≤ 1 / 2 := by
    have : (1 - (W : ℤ)) ≤ -1 := by omega
    calc (2 : ℝ) ^ (1 - (W : ℤ)) ≤ 2 ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) this
      _ = 1 / 2 := by norm_num
  have hpos : ∀ t, 0 < (1 + δ t) * (1 - r t) := fun t => by
    have := hr t; have := hδ t
    exact mul_pos (by linarith) (by linarith)
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hterm : ∀ t, |Real.logb 2 ((1 + δ t) * (1 - r t))| ≤
      2 ^ (3 - (W : ℤ)) + 2 ^ (2 - (R : ℤ)) := by
    intro t
    obtain ⟨hr0, hr1⟩ := hr t
    obtain ⟨hδ0, hδ1⟩ := hδ t
    have hrl := (rebase_log_residual).2 (r := r t) (W := W) hW hr0 hr1
    have h1r : 0 < 1 - r t := by linarith
    have h1δ : 0 < 1 + δ t := by linarith
    rw [Real.logb_mul h1δ.ne' h1r.ne']
    have hδlog : |Real.logb 2 (1 + δ t)| ≤ 2 ^ (2 - (R : ℤ)) := by
      have hlog0 : 0 ≤ Real.log (1 + δ t) := Real.log_nonneg (by linarith)
      have hlogle : Real.log (1 + δ t) ≤ δ t := by
        have := Real.log_le_sub_one_of_pos h1δ; linarith
      rw [Real.logb, abs_div, abs_of_nonneg hlog0, abs_of_pos (by linarith : (0:ℝ) < Real.log 2),
        div_le_iff₀ (by linarith)]
      have e2 : (2 : ℝ) ^ (2 - (R : ℤ)) = 2 * 2 ^ (1 - (R : ℤ)) := by
        rw [show (2 - (R : ℤ)) = 1 + (1 - (R : ℤ)) by ring, zpow_add₀ (by norm_num)]
        norm_num
      rw [e2]
      have : (0 : ℝ) ≤ 2 ^ (1 - (R : ℤ)) := by positivity
      nlinarith
    calc |Real.logb 2 (1 + δ t) + Real.logb 2 (1 - r t)|
        ≤ |Real.logb 2 (1 + δ t)| + |Real.logb 2 (1 - r t)| := abs_add_le _ _
      _ ≤ 2 ^ (2 - (R : ℤ)) + 2 ^ (3 - (W : ℤ)) := add_le_add hδlog hrl.le
      _ = 2 ^ (3 - (W : ℤ)) + 2 ^ (2 - (R : ℤ)) := by ring
  rw [Real.logb_prod _ _ fun t _ => (hpos t).ne']
  calc |∑ t ∈ Finset.range n, Real.logb 2 ((1 + δ t) * (1 - r t))|
      ≤ ∑ t ∈ Finset.range n, |Real.logb 2 ((1 + δ t) * (1 - r t))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range n, (2 ^ (3 - (W : ℤ)) + 2 ^ (2 - (R : ℤ)) : ℝ) :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = n * (2 ^ (3 - (W : ℤ)) + 2 ^ (2 - (R : ℤ))) := by simp [mul_add]

/-- [proved-derived; formal-checked] **`width_or_rebase_total`: the carrier fits, or rebases.** For
operands `a < 2^(w_a)` and `b < 2^(w_b)` and a carrier of `W` bits:
* when `w_a + w_b ≤ W` the product fits exactly, `a b < 2^W`;
* at any `e` with `w_a + w_b ≤ W + e` the rebased product fits, `a ⌊b/2^e⌋ < 2^W`;
* a `w_b`-bit `b` (`2^(w_b − 1) ≤ b`) rebased at `e < w_b` keeps `⌊b/2^e⌋ ≥ 2^(w_b − 1 − e)`, and
  its released relative width `b/(2^e ⌊b/2^e⌋) − 1` is below `1/⌊b/2^e⌋`;
* over `n` steps whose kept parts `D̂_t` have at least `R` bits, the released widths sum to at most
  `n 2^(1−R)`. -/
theorem width_or_rebase_total (W wa wb a b : ℕ) (ha : a < 2 ^ wa) (hb : b < 2 ^ wb) :
    (wa + wb ≤ W → a * b < 2 ^ W) ∧
      (∀ e, wa + wb ≤ W + e → a * (b / 2 ^ e) < 2 ^ W) ∧
      (∀ e, e < wb → 2 ^ (wb - 1) ≤ b →
        2 ^ (wb - 1 - e) ≤ b / 2 ^ e ∧
          (b : ℚ) / (2 ^ e * (b / 2 ^ e : ℕ)) - 1 < 1 / ((b / 2 ^ e : ℕ) : ℚ)) ∧
      ∀ (R n : ℕ) (kept : ℕ → ℕ), (∀ t, 2 ^ (R - 1) ≤ kept t) → 1 ≤ R →
        ∑ t ∈ Finset.range n, (1 : ℚ) / kept t ≤ n * (2 : ℚ) ^ (1 - (R : ℤ)) := by
  refine ⟨fun h => ?_, fun e h => ?_, fun e he hbig => ⟨?_, ?_⟩, fun R n kept hk hR => ?_⟩
  · calc a * b < 2 ^ wa * 2 ^ wb := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ (wa + wb) := (pow_add 2 wa wb).symm
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h
  · by_cases hle : wb ≤ e
    · have : b / 2 ^ e = 0 := by
        apply Nat.div_eq_of_lt
        calc b < 2 ^ wb := hb
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hle
      rw [this, mul_zero]
      exact Nat.two_pow_pos W
    · have hq : b / 2 ^ e < 2 ^ (wb - e) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos e), ← pow_add]
        rwa [Nat.sub_add_cancel (by omega)]
      calc a * (b / 2 ^ e) ≤ a * (2 ^ (wb - e)) := Nat.mul_le_mul_left a hq.le
        _ < 2 ^ wa * 2 ^ (wb - e) := by
          apply Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _)
        _ = 2 ^ (wa + (wb - e)) := (pow_add 2 wa _).symm
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos e), ← pow_add]
    rwa [show wb - 1 - e + e = wb - 1 by omega]
  · have hpos : 0 < b / 2 ^ e := by
      have h1 : 1 ≤ 2 ^ (wb - 1 - e) := Nat.one_le_two_pow
      have h2 : 2 ^ (wb - 1 - e) ≤ b / 2 ^ e := by
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos e), ← pow_add]
        rwa [show wb - 1 - e + e = wb - 1 by omega]
      omega
    have hk : (0 : ℚ) < ((b / 2 ^ e : ℕ) : ℚ) := by exact_mod_cast hpos
    have hp : (0 : ℚ) < 2 ^ e := by positivity
    have hdec := (Nat.div_add_mod b (2 ^ e)).symm
    have hr : b % 2 ^ e < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos e)
    have eb : (b : ℚ) = 2 ^ e * ((b / 2 ^ e : ℕ) : ℚ) + ((b % 2 ^ e : ℕ) : ℚ) := by
      exact_mod_cast hdec
    have er : ((b % 2 ^ e : ℕ) : ℚ) < 2 ^ e := by exact_mod_cast hr
    rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity), eb]
    have : (1 / ((b / 2 ^ e : ℕ) : ℚ) + 1) * (2 ^ e * ((b / 2 ^ e : ℕ) : ℚ)) =
        2 ^ e + 2 ^ e * ((b / 2 ^ e : ℕ) : ℚ) := by field_simp
    rw [this]
    linarith
  · have hterm : ∀ t, (1 : ℚ) / kept t ≤ (2 : ℚ) ^ (1 - (R : ℤ)) := by
      intro t
      have hkt : (2 : ℚ) ^ (R - 1) ≤ kept t := by exact_mod_cast hk t
      have hp : (0 : ℚ) < 2 ^ (R - 1) := by positivity
      have e1 : (2 : ℚ) ^ (1 - (R : ℤ)) = 1 / 2 ^ (R - 1) := by
        rw [show (1 - (R : ℤ)) = -((R - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, one_div]
      rw [e1]
      exact one_div_le_one_div_of_le hp hkt
    calc ∑ t ∈ Finset.range n, (1 : ℚ) / kept t ≤ ∑ _t ∈ Finset.range n, (2 : ℚ) ^ (1 - (R : ℤ)) :=
          Finset.sum_le_sum fun t _ => hterm t
      _ = n * (2 : ℚ) ^ (1 - (R : ℤ)) := by simp

section Audit

#print axioms rebase_decode
#print axioms rebase_ratio_enclosed
#print axioms rebase_step_enclosed
#print axioms rebase_log_residual_sum
#print axioms width_or_rebase_total

end Audit

end Holonics.HNN.LandmarkCarrier
