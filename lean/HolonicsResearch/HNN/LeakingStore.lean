import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# A leaking store: its release, its rest, its contraction, its own comparison and the order it holds

Atlas: `store.leak-founded-by-own-news`, `contact.leaking-circle-word-polynomial`. Record:
`research/records/2026-11-21_A_STORES_LEAK_IS_FOUNDED_BY_ITS_OWN_NEWS_…` (§3 to §6).

A store that takes an arrival a tick, `x ← γ x + g` with `γ = 1/(1 + d)`, is the engine's one move
`(M, J) ← (γ M + m, γ J + m c)` released once as `J/M` (THE_ENGINE §2). The built tick is the end `γ = 1`. This module
holds the algebra the record's law rests on, one coordinate at a time.

1. **The pair and its release** (`release_leak`, `release_step`): a leak releases mass and keeps the ratio, and the
   release after an arrival moves by the news, the arrival less the release, at the gain `m/M′`. So a leak of the pair
   and a news write of the release are one move.
2. **The rest** (`rest_mass`, `rest_mass_drift`): what arrives equals what leaves at `M = m(1 + d)/d`, the reach of
   `store.finite-quality`; where the friction is a drift times the mass held, `d = qM`, at `q M² = m(1 + qM)`.
3. **The built tick on its fill** (`chart_ratio`, `chart_step_ratio`): a mode of exponent `ν` at fill `F` changes its
   place on the chart by `(F + ν)/(F + 1)` a tick and its successive moves by `(F + ν)/(F + 2)`.
4. **Under a leak** (`leak_multiplier`, `leak_contracts`, `leak_boost_iff`, `balance_point`, `leak_minimax`): at the
   rest fill `1/δ` the mode's multiplier is `1 − δ(1 − ν)`; it contracts for every `0 < δ ≤ 1` where `−1 < ν < 1`, and
   it grows exactly where `ν > 1`; the two end modes are equal and opposite at `δ = 2/(a + b)`, and no leak makes
   both smaller than `(b − a)/(b + a)` (the bound attained there is `HNN/CarriedRate.plain_step`).
5. **The store's own comparison** (`news_sq`, `news_gain_step`, `news_orthogonal_iff`, `news_least`,
   `lag_one_zero_iff`): the next news after a step of gain `K` along this news is `a − K b`; a change `h` of the gain
   changes its power by `−2h⟨a − K b, b⟩ + h²‖b‖²`, so the inner product of successive news is the descent covector
   of the gain; the next news is least exactly where the two are orthogonal.
6. **The order a leaking store holds** (`store`, `store_eq_sum`, `same_last_side`, `same_first_side`,
   `third_turn_cycle`): from rest the store holds its arrivals as their word's polynomial at the multiplier; two
   orders of three arrivals that share their last differ by `(γ − γ²)` times the difference of the two swapped, two
   that share their first by `(1 − γ)` times it, so the six orders stand on a hexagon whose sides alternate in the
   ratio `γ`; at a multiplier that is a turn by a third a cyclic change of the order turns the holding by a third.

Limits. Vectors are read one coordinate at a time except in part 5; the fixed ray, the linearization about it and
the non-normal transient are the record's and are not stated; `lag_one_zero_iff` is the algebra of the lag-one
covariance of a level's news under a fixed gain, `P − K S` with `S = P + r` (Mehra 1970, from training), and the
covariance itself is not stated.
-/

open scoped InnerProductSpace

namespace Holonics.HNN.LeakingStore

/-! ## 1. The pair and its release -/

/-- [proved-standard; formal-checked] A leak releases mass and keeps the ratio: where no arrival comes, the release
`x/M` stands at every `γ`. -/
theorem release_leak (γ M x : ℝ) (hγ : γ ≠ 0) : γ * x / (γ * M) = x / M :=
  mul_div_mul_left x M hγ

/-- [proved-standard; formal-checked] **A leak of the pair is a news write of the release**: after an arrival of
mass `m` and value `g`, the release has moved by the news `g − x/M` at the gain `m/(γ M + m)`. -/
theorem release_step (γ M m x g : ℝ) (hM : M ≠ 0) (hM' : γ * M + m ≠ 0) :
    (γ * x + m * g) / (γ * M + m) = x / M + m / (γ * M + m) * (g - x / M) := by
  field_simp
  ring

/-! ## 2. The rest -/

/-- [proved-standard; formal-checked] **What arrives equals what leaves** at the mass `m (1 + d)/d`: the reach of
`store.finite-quality` is the store's quality at rest. -/
theorem rest_mass (d m M : ℝ) (hd : 0 < d) : M = M / (1 + d) + m ↔ M = m * (1 + d) / d := by
  have h1 : (1 + d) ≠ 0 := by positivity
  rw [div_add' _ _ _ h1, eq_div_iff h1, eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- [proved-standard; formal-checked] Where the friction is a drift times the mass held, `d = q M`, the rest is at
`q M² = m (1 + q M)`. -/
theorem rest_mass_drift (q m M : ℝ) (h : 1 + q * M ≠ 0) :
    M = M / (1 + q * M) + m ↔ q * M ^ 2 = m * (1 + q * M) := by
  rw [div_add' _ _ _ h, eq_div_iff h]
  constructor <;> intro e <;> linear_combination e

/-! ## 3. The built tick on its fill -/

/-- [proved-standard; formal-checked] A transverse part `ρ` at fill `F` that the tick moves by `ν ρ/F` stands on the
chart, after the fill has grown by one, at `(F + ν)/(F + 1)` of where it stood. -/
theorem chart_ratio (F ν ρ : ℝ) (hF : F ≠ 0) (hF1 : F + 1 ≠ 0) :
    (ρ + ν * (ρ / F)) / (F + 1) = ρ / F * ((F + ν) / (F + 1)) := by
  field_simp

/-- [proved-standard; formal-checked] **Successive moves of the chart stand in the ratio `(F + ν)/(F + 2)`.** -/
theorem chart_step_ratio (F ν : ℝ) (hF1 : F + 1 ≠ 0) (hF2 : F + 2 ≠ 0) :
    (F + ν) / (F + 1) * ((F + 1 + ν) / (F + 2)) - (F + ν) / (F + 1) =
      (F + ν) / (F + 2) * ((F + ν) / (F + 1) - 1) := by
  field_simp
  ring

/-! ## 4. Under a leak -/

/-- [proved-standard; formal-checked] At the rest fill `1/δ` a mode of exponent `ν` is multiplied by
`1 − δ (1 − ν)` a tick. -/
theorem leak_multiplier (δ ν : ℝ) : (1 - δ) + ν / (1 / δ) = 1 - δ * (1 - ν) := by
  rw [one_div, div_inv_eq_mul]
  ring

/-- [proved-standard; formal-checked] **Every mode whose exponent is under one contracts under a leak**, at every
strength up to replacement. -/
theorem leak_contracts (δ ν : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hν1 : ν < 1) (hν : -1 < ν) :
    |1 - δ * (1 - ν)| < 1 := by
  have h0 : 0 < δ * (1 - ν) := mul_pos hδ0 (by linarith)
  have h2 : δ * (1 - ν) ≤ 1 * (1 - ν) := mul_le_mul_of_nonneg_right hδ1 (by linarith)
  rw [abs_lt]
  constructor <;> linarith

/-- [proved-standard; formal-checked] A leak leaves a growth exactly where the exponent is over one. -/
theorem leak_boost_iff (δ ν : ℝ) (hδ : 0 < δ) : 1 < 1 - δ * (1 - ν) ↔ 1 < ν := by
  constructor
  · intro h
    by_contra hν
    have hν := not_lt.mp hν
    have : 0 ≤ δ * (1 - ν) := mul_nonneg hδ.le (by linarith)
    linarith
  · intro h
    have : 0 < δ * (ν - 1) := mul_pos hδ (by linarith)
    linarith

/-- [proved-standard; formal-checked] The two end modes, of exponents `1 − a` and `1 − b`, are equal and opposite
exactly at `δ = 2/(a + b)`. -/
theorem balance_point (a b δ : ℝ) (hab : a + b ≠ 0) : 1 - δ * a = -(1 - δ * b) ↔ δ = 2 / (a + b) := by
  rw [eq_div_iff hab]
  constructor <;> intro h <;> linarith

/-- [proved-standard; formal-checked] **No leak makes both end modes smaller than `(b − a)/(b + a)`.** -/
theorem leak_minimax (a b δ : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / (b + a) ≤ max |1 - δ * a| |1 - δ * b| := by
  by_contra h
  have h := not_le.mp h
  obtain ⟨h1, h2⟩ := max_lt_iff.mp h
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpos : 0 < b + a := by linarith
  rw [lt_div_iff₀ hpos] at h1 h2
  have e1 : (1 - δ * a) * (b + a) < b - a :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le) h1
  have e2 : -(1 - δ * b) * (b + a) < b - a :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (neg_le_abs _) hpos.le) h2
  have k1 : 2 < δ * (b + a) := by
    by_contra hk
    have hk := not_lt.mp hk
    nlinarith [mul_le_mul_of_nonneg_left hk ha.le]
  have k2 : δ * (b + a) < 2 := by
    by_contra hk
    have hk := not_lt.mp hk
    nlinarith [mul_le_mul_of_nonneg_left hk hb.le]
  linarith

/-! ## 5. The store's own comparison -/

section News

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-standard; formal-checked] The power of the next news after a step of gain `K` along this news `b`,
`a` the next news had the store not moved. -/
theorem news_sq (a b : E) (K : ℝ) :
    ‖a - K • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * K * ⟪a, b⟫_ℝ + K ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- [proved-standard; formal-checked] **The inner product of successive news is the gain's descent covector**: a
change `h` of the gain changes the next news' power by `−2h⟨a − K b, b⟩ + h²‖b‖²`. -/
theorem news_gain_step (a b : E) (K h : ℝ) :
    ‖a - (K + h) • b‖ ^ 2 = ‖a - K • b‖ ^ 2 - 2 * h * ⟪a - K • b, b⟫_ℝ + h ^ 2 * ‖b‖ ^ 2 := by
  have e : a - (K + h) • b = (a - K • b) - h • b := by
    rw [add_smul]
    abel
  rw [e, news_sq]

/-- [proved-standard; formal-checked] Successive news are orthogonal exactly at the gain `⟨a, b⟩/‖b‖²`. -/
theorem news_orthogonal_iff (a b : E) (K : ℝ) (hb : b ≠ 0) :
    ⟪a - K • b, b⟫_ℝ = 0 ↔ K = ⟪a, b⟫_ℝ / ‖b‖ ^ 2 := by
  have hB : ‖b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hb)
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, sub_eq_zero, eq_div_iff hB]
  exact eq_comm

/-- [proved-standard; formal-checked] **The next news is least where it is orthogonal to this one.** -/
theorem news_least (a b : E) (K : ℝ) (hb : b ≠ 0) :
    ‖a - (⟪a, b⟫_ℝ / ‖b‖ ^ 2) • b‖ ^ 2 ≤ ‖a - K • b‖ ^ 2 := by
  have hB : 0 < ‖b‖ ^ 2 := pow_pos (norm_pos_iff.mpr hb) 2
  have h := news_gain_step a b (⟪a, b⟫_ℝ / ‖b‖ ^ 2) (K - ⟪a, b⟫_ℝ / ‖b‖ ^ 2)
  rw [add_sub_cancel, (news_orthogonal_iff a b _ hb).mpr rfl] at h
  rw [h]
  nlinarith [mul_nonneg (sq_nonneg (K - ⟪a, b⟫_ℝ / ‖b‖ ^ 2)) hB.le]

end News

/-- [proved-standard; formal-checked] The algebra of a level's news under a fixed gain: with `P` the power of what
the store has not yet followed and `r` the arrival's own noise, `P − K (P + r)` is zero exactly at the gain
`1 − r/(P + r)`, the share of the news that is not noise. -/
theorem lag_one_zero_iff (P r K : ℝ) (hS : P + r ≠ 0) : P - K * (P + r) = 0 ↔ K = 1 - r / (P + r) := by
  rw [sub_eq_zero, one_sub_div hS, eq_div_iff hS]
  constructor <;> intro h <;> linarith

/-! ## 6. The order a leaking store holds -/

section Word

variable {R : Type*} [CommRing R]

/-- A store from rest: each tick it keeps `γ` of what it holds and takes the arrival. -/
def store (γ : R) (g : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => γ * store γ g n + g n

/-- [proved-standard; formal-checked] **A leaking store holds its arrivals as their word's polynomial at the
multiplier**: the arrival of age `j` at the weight `γ^j`. -/
theorem store_eq_sum (γ : R) (g : ℕ → R) (n : ℕ) :
    store γ g n = ∑ j ∈ Finset.range n, γ ^ (n - 1 - j) * g j := by
  induction n with
  | zero => simp [store]
  | succ n ih =>
    rw [store, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < n := Finset.mem_range.mp hj
      have e : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
      rw [e, pow_succ]
      ring
    · simp

/-- [proved-standard; formal-checked] Two orders of three arrivals that share their last differ by `γ − γ²` times
the difference of the two they swap. -/
theorem same_last_side (γ l p q : R) :
    (l + γ * p + γ ^ 2 * q) - (l + γ * q + γ ^ 2 * p) = (γ - γ ^ 2) * (p - q) := by
  ring

/-- [proved-standard; formal-checked] Two orders that share their first differ by `1 − γ` times it: the six orders'
sides alternate in the ratio `γ`. -/
theorem same_first_side (γ f p q : R) :
    (p + γ * q + γ ^ 2 * f) - (q + γ * p + γ ^ 2 * f) = (1 - γ) * (p - q) := by
  ring

/-- [proved-standard; formal-checked] **At a multiplier that is a turn by a third, a cyclic change of the order
turns the holding by a third.** -/
theorem third_turn_cycle (ω a b c : R) (h : ω ^ 3 = 1) :
    b + ω * c + ω ^ 2 * a = ω ^ 2 * (a + ω * b + ω ^ 2 * c) := by
  linear_combination (-(b + ω * c)) * h

end Word

end Holonics.HNN.LeakingStore
