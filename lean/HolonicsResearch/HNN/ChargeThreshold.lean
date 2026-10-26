import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The charge threshold falls with evidence

The record `research/records/2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md`
(§1 "When it becomes compute", receipt part F; atlas `contact.charge-falls-with-evidence`) reads
the least relative drop `δ` a lap certifies on `N` observations from a pool of `P` candidates as the
least `δ` with `(1/(1 − δ))^N > N P²`, and computed it at `P = 2¹⁰` by an exact search over
`δ = 1/m`. #410 owes the law; this file proves it.

[proved-derived; formal-checked] What is proved.

1. **The threshold** (`chargeThreshold`, `certifies_iff`, `certifies_iff_threshold`): for `N ≥ 1`,
   `c > 0` and `δ < 1`, `c < (1/(1 − δ))^N` exactly when `δ > 1 − c^(−1/N)`. With `c = N P²` the
   drops a lap certifies are the open ray above `δ_min(N) = 1 − (N P²)^(−1/N)`.
2. **Its size** (`chargeThreshold_eq_exp`, `chargeThreshold_nonneg`, `chargeThreshold_le`):
   `δ_min(N) = 1 − exp(−(ln N + 2 ln P)/N)`, so `0 ≤ δ_min(N) ≤ (ln N + 2 ln P)/N`
   (from `1 − e^(−t) ≤ t`).
3. **It falls strictly with evidence** (`chargeThreshold_succ_lt`, `charge_threshold_antitone`):
   for `P ≥ 2` and `1 ≤ M < N`, `δ_min(N) < δ_min(M)`, because `N ln(1 + 1/N) ≤ 1 < ln(N P²)` once
   `N P² ≥ 4 > e`.
4. **It tends to zero** (`chargeThreshold_tendsto_zero`).
5. **The receipts** (`certifies_one_div`, `threshold_bracket`, `threshold_thousand`,
   `threshold_ten_thousand`, `threshold_hundred_thousand`): `δ = 1/m` certifies exactly when
   `(m − 1)^N · N P² < m^N`; at `P = 2¹⁰` the largest such `m` is `48`, `433` and `3941` at
   `N = 10³, 10⁴, 10⁵`, so `δ_min` lies in `[1/49, 1/48)`, `[1/434, 1/433)` and
   `[1/3942, 1/3941)`. The integer comparisons are decided exactly.

Consumers: the atlas row `contact.charge-falls-with-evidence`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ChargeThreshold

open Filter

/-- [definition] The least relative drop a lap certifies on `N` observations from a pool of `P`
candidates: `δ_min(N) = 1 − (N P²)^(−1/N)`. -/
noncomputable def chargeThreshold (P N : ℕ) : ℝ := 1 - ((N : ℝ) * P ^ 2) ^ (-(N : ℝ)⁻¹)

/-- [proved-derived; formal-checked] **The drops a lap certifies are the ray above the threshold:**
`c < (1/(1 − δ))^N ↔ 1 − c^(−1/N) < δ`. -/
theorem certifies_iff {N : ℕ} (hN : 0 < N) {c δ : ℝ} (hc : 0 < c) (hδ : δ < 1) :
    c < (1 / (1 - δ)) ^ N ↔ 1 - c ^ (-(N : ℝ)⁻¹) < δ := by
  have hu : 0 < 1 - δ := by linarith
  have hx : 0 < 1 / (1 - δ) := one_div_pos.2 hu
  obtain ⟨r, hr0, hrN, hneg⟩ : ∃ r : ℝ, 0 < r ∧ r ^ N = c ∧ c ^ (-(N : ℝ)⁻¹) = r⁻¹ :=
    ⟨c ^ ((N : ℝ)⁻¹), Real.rpow_pos_of_pos hc _, Real.rpow_inv_natCast_pow hc.le hN.ne',
      Real.rpow_neg hc.le _⟩
  have hpow : r ^ N < (1 / (1 - δ)) ^ N ↔ r < 1 / (1 - δ) :=
    ⟨lt_of_pow_lt_pow_left₀ N hx.le, fun h => pow_lt_pow_left₀ h hr0.le hN.ne'⟩
  rw [hneg, ← hrN, hpow, lt_one_div hr0 hu, one_div, sub_lt_comm]

/-- [proved-derived; formal-checked] With `c = N P²`: `N P² < (1/(1 − δ))^N ↔ δ_min(N) < δ`. -/
theorem certifies_iff_threshold {P N : ℕ} (hN : 0 < N) (hP : 0 < P) {δ : ℝ} (hδ : δ < 1) :
    (N : ℝ) * P ^ 2 < (1 / (1 - δ)) ^ N ↔ chargeThreshold P N < δ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  rw [chargeThreshold]
  exact certifies_iff hN (mul_pos hN' (pow_pos hP' 2)) hδ

/-- [proved-derived; formal-checked] `δ_min(N) = 1 − exp(−(ln N + 2 ln P)/N)`. -/
theorem chargeThreshold_eq_exp {P N : ℕ} (hN : 0 < N) (hP : 0 < P) :
    chargeThreshold P N = 1 - Real.exp (-((Real.log N + 2 * Real.log P) / N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  rw [chargeThreshold, Real.rpow_def_of_pos (mul_pos hN' (pow_pos hP' 2)),
    Real.log_mul hN'.ne' (pow_ne_zero 2 hP'.ne'), Real.log_pow]
  congr 2
  push_cast
  ring

/-- [proved-derived; formal-checked] `δ_min(N) ≥ 0`. -/
theorem chargeThreshold_nonneg {P N : ℕ} (hN : 0 < N) (hP : 0 < P) : 0 ≤ chargeThreshold P N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have ha : 0 ≤ (Real.log N + 2 * Real.log P) / N :=
    div_nonneg (by linarith [Real.log_nonneg hN1, Real.log_nonneg hP1]) hN'.le
  rw [chargeThreshold_eq_exp hN hP]
  have := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
  linarith

/-- [proved-derived; formal-checked] **`δ_min(N) ≤ (ln N + 2 ln P)/N`.** -/
theorem chargeThreshold_le {P N : ℕ} (hN : 0 < N) (hP : 0 < P) :
    chargeThreshold P N ≤ (Real.log N + 2 * Real.log P) / N := by
  rw [chargeThreshold_eq_exp hN hP]
  have := Real.add_one_le_exp (-((Real.log N + 2 * Real.log P) / N))
  linarith

/-- `e < 4`, from `1 − t < e^(−t)` at `t = 1/2`. -/
theorem exp_one_lt_four : Real.exp 1 < 4 := by
  have h1 : (1 : ℝ) / 2 < Real.exp (-(1 / 2)) := by
    have := Real.add_one_lt_exp (show (-(1 / 2) : ℝ) ≠ 0 by norm_num)
    linarith
  have hmul : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos := Real.exp_pos (1 / 2)
  have h2 : Real.exp (1 / 2) < 2 := by nlinarith
  have hsq : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  rw [hsq]
  nlinarith

/-- [proved-derived; formal-checked] **One more observation lowers the threshold** when `P ≥ 2`. -/
theorem chargeThreshold_succ_lt {P N : ℕ} (hN : 0 < N) (hP : 2 ≤ P) :
    chargeThreshold P (N + 1) < chargeThreshold P N := by
  have hP0 : 0 < P := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hN0 : (N : ℝ) ≠ 0 := hN'.ne'
  have hPpos : (0 : ℝ) < P := by linarith
  rw [chargeThreshold_eq_exp (show 0 < N + 1 by omega) hP0, chargeThreshold_eq_exp hN hP0]
  push_cast
  -- `ln(N P²) > 1`, since `N P² ≥ 4 > e`
  have hL : 1 < Real.log N + 2 * Real.log P := by
    have hP4 : (4 : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith
    have hc4 : (4 : ℝ) ≤ (N : ℝ) * P ^ 2 := by
      have := mul_le_mul hN1 hP4 (by norm_num) (by linarith)
      linarith
    have h := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le exp_one_lt_four hc4)
    rw [Real.log_exp, Real.log_mul hN0 (pow_ne_zero 2 hPpos.ne'), Real.log_pow] at h
    push_cast at h
    linarith
  -- `ln(N + 1) ≤ ln N + 1/N`
  have hstep : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 / N := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N from
      div_pos (by linarith) hN')
    rw [Real.log_div (by positivity) hN0] at h
    have e : ((N : ℝ) + 1) / N = 1 + 1 / N := by rw [add_div, div_self hN0]
    linarith
  have key : (Real.log ((N : ℝ) + 1) + 2 * Real.log P) / ((N : ℝ) + 1) <
      (Real.log N + 2 * Real.log P) / N := by
    rw [lt_div_iff₀ hN', div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    have h1 := mul_le_mul_of_nonneg_right hstep hN'.le
    have e : (Real.log N + 1 / N) * N = Real.log N * N + 1 := by
      rw [add_mul, one_div, inv_mul_cancel₀ hN0]
    linarith
  have := Real.exp_lt_exp.2 (neg_lt_neg key)
  linarith

/-- [proved-derived; formal-checked] **The threshold falls strictly with evidence:** for `P ≥ 2`
and `1 ≤ M < N`, `δ_min(N) < δ_min(M)`. -/
theorem charge_threshold_antitone {P : ℕ} (hP : 2 ≤ P) {M N : ℕ} (hM : 0 < M) (hMN : M < N) :
    chargeThreshold P N < chargeThreshold P M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hMN
  clear hMN
  induction k with
  | zero => simpa using chargeThreshold_succ_lt hM hP
  | succ k ih =>
    have h := chargeThreshold_succ_lt (N := M + k + 1) (by omega) hP
    rw [show M + (k + 1) + 1 = M + k + 1 + 1 by ring]
    exact h.trans ih

/-- [proved-derived; formal-checked] **The threshold tends to zero.** -/
theorem chargeThreshold_tendsto_zero {P : ℕ} (hP : 0 < P) :
    Tendsto (fun N : ℕ => chargeThreshold P N) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N / N) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa using h
  have hup : Tendsto (fun N : ℕ => (Real.log N + 2 * Real.log P) / N) atTop (nhds 0) := by
    have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 * Real.log P)
    simpa [add_div] using hlog.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact chargeThreshold_nonneg hN hP
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact chargeThreshold_le hN hP

/-- [proved-derived; formal-checked] **`δ = 1/m` certifies exactly when
`(m − 1)^N · N P² < m^N`**, an integer comparison. -/
theorem certifies_one_div {N P m : ℕ} (hm : 2 ≤ m) :
    (N : ℝ) * P ^ 2 < (1 / (1 - 1 / (m : ℝ))) ^ N ↔ (m - 1) ^ N * (N * P ^ 2) < m ^ N := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := (show (0 : ℝ) < m by linarith).ne'
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hfrac : 1 / (1 - 1 / (m : ℝ)) = m / ((m : ℝ) - 1) := by
    rw [one_sub_div hm0, one_div_div]
  rw [hfrac, div_pow, lt_div_iff₀ (pow_pos hm1 N), ← Nat.cast_lt (α := ℝ)]
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **The bracket from one integer search step:** if `δ = 1/m`
certifies and `δ = 1/(m + 1)` does not, then `1/(m + 1) ≤ δ_min(N) < 1/m`. -/
theorem threshold_bracket {N P m : ℕ} (hN : 0 < N) (hP : 0 < P) (hm : 2 ≤ m)
    (hyes : (m - 1) ^ N * (N * P ^ 2) < m ^ N) (hno : ¬ m ^ N * (N * P ^ 2) < (m + 1) ^ N) :
    1 / ((m : ℝ) + 1) ≤ chargeThreshold P N ∧ chargeThreshold P N < 1 / m := by
  have hδ : ∀ k : ℕ, 2 ≤ k → (1 : ℝ) / k < 1 := by
    intro k hk
    have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    rw [div_lt_one (by linarith)]
    exact hk'
  constructor
  · have hno' : ¬ (N : ℝ) * P ^ 2 < (1 / (1 - 1 / ((m + 1 : ℕ) : ℝ))) ^ N := by
      rw [certifies_one_div (m := m + 1) (by omega), Nat.add_sub_cancel]
      exact hno
    rw [certifies_iff_threshold hN hP (hδ (m + 1) (by omega))] at hno'
    push_cast at hno'
    exact not_lt.1 hno'
  · exact (certifies_iff_threshold hN hP (hδ m hm)).1 ((certifies_one_div hm).2 hyes)

/-- [proved-derived; formal-checked] **At `P = 2¹⁰`, `N = 10³`:** `1/49 ≤ δ_min < 1/48`. -/
theorem threshold_thousand :
    1 / ((48 : ℝ) + 1) ≤ chargeThreshold (2 ^ 10) 1000 ∧
      chargeThreshold (2 ^ 10) 1000 < 1 / (48 : ℝ) := by
  have h := threshold_bracket (N := 1000) (P := 2 ^ 10) (m := 48) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide)
  exact_mod_cast h

/-- [proved-derived; formal-checked] **At `P = 2¹⁰`, `N = 10⁴`:** `1/434 ≤ δ_min < 1/433`. -/
theorem threshold_ten_thousand :
    1 / ((433 : ℝ) + 1) ≤ chargeThreshold (2 ^ 10) 10000 ∧
      chargeThreshold (2 ^ 10) 10000 < 1 / (433 : ℝ) := by
  have h := threshold_bracket (N := 10000) (P := 2 ^ 10) (m := 433) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide)
  exact_mod_cast h

/-- [proved-derived; formal-checked] **At `P = 2¹⁰`, `N = 10⁵`:** `1/3942 ≤ δ_min < 1/3941`. -/
theorem threshold_hundred_thousand :
    1 / ((3941 : ℝ) + 1) ≤ chargeThreshold (2 ^ 10) 100000 ∧
      chargeThreshold (2 ^ 10) 100000 < 1 / (3941 : ℝ) := by
  have h := threshold_bracket (N := 100000) (P := 2 ^ 10) (m := 3941) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide)
  exact_mod_cast h

end Holonics.HNN.ChargeThreshold
