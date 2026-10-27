import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# The tower's certified section and its moments

The record
`research/records/2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO.md`
(atlas `hnn.tower-certified-section`) deposits a section's step only when the section, reread from
its opening states, codes strictly fewer bits; a refused step halves until it is certified or
releases to zero (`hnn::tower::TowerLearner::section`). The certificate is decided by partition:
summed integer readings of `log₂` decide outside a band of every reading's slack, and the exact
products decide inside it (`hnn::tower::fewer_bits`). The covector's moments move by
`m ← m + release(g − m, r)`, and by one grain toward `g` when that release is zero
(`hnn::tower::toward`). #410 owes that the certified step strictly lowers the section's code, and
that the moment law reaches a constant input exactly, so a silent contact's step reaches zero.

[proved-derived; formal-checked] What is proved.

1. **The release** (`release`, `hnn::keyed_modes::release`: `x` released `b` coarser, to the
   nearest numerator, half away from zero). It is odd (`release_neg`), keeps the sign and never
   passes its argument (`release_bounds_of_nonneg`, `release_bounds_of_nonpos`), is zero once
   `2|x| < 2^b` (`release_eq_zero`, `release_eq_zero_of_natAbs`), and so every finite step releases
   to zero after finitely many halvings (`halving_ends`, `halving_stops`).
2. **The moment law arrives** (`toward`). One move from `m ≠ g` moves strictly toward `g` and never
   passes it (`toward_of_lt`, `toward_of_gt`); at `g` it stays (`toward_self`). So the moment
   reaches a constant input `g` within `|g − m|` sections and stays there (`toward_iterate`).
   For a silent contact (`g = 0`, and `g² = 0` for the second moment) both moments reach zero
   (`silent_moment_reaches_zero`), and the step `((m ≪ grain) ≫ rate) / (⌊√v⌋ + 1)`
   (`depositStep`, `hnn::tower::deposit_step`) is zero from then on whatever `v` is
   (`silent_step_reaches_zero`).
3. **The exact certificate is the code's strict fall** (`fewerBitsExact_iff`): for faces
   `p = m/t` with positive masses and totals, `Π m_new · Π t_old > Π m_old · Π t_new` iff
   `Σ −log₂ p_new < Σ −log₂ p_old`.
4. **The partition decides as the products do** (`fewerBits_iff`): for any integer reading `ρ`
   with `|ρ(v) − G log₂ v| ≤ s` on every positive `v` (`G > 0` the grains a bit), a side's summed
   reading lies within `2 s` a face of `−G` times its code (`side_close`); so a difference of
   summed readings past `2 s (a + b)` decides the comparison (`readings_decide_fewer`,
   `readings_decide_not_fewer`), and the whole partitioned decision, with a zero mass or total
   sent to the products, is the exact comparison in every case. A certified step strictly lowers
   the section's code (`certified_lowers_code`).
5. **The section** (`section_deposit`): halving from the proposed step, the section stops at the
   first count of halvings at which nothing moves or the certificate holds, and stops at all;
   when it deposits, the step it deposits is certified and the reread code is strictly below the
   opening's. A section therefore never raises its code.

The reading's own bound is the hypothesis of item 4: the Rust `log2_reading` lies below `log₂ v`
by less than one grain of `2^(−32)` (its docstring's unrolled squarings), inside the slack of three
grains, and the test `the_certificate_decided_by_partition_is_the_exact_comparison` reads it. The
moment law here is the integer law; its carrier's width (the Rust `i128` and its refusals) is not
modelled.

The computational object is the helical pair interaction's deposition: a contact's covector moves
its moments, and the constitution changes only by a certified step, read on the section the step
was taken from. Of the winding guide's six general objects this touches faces and placement (the
section's faces, read at the receiver) and the tower thread (a section of the tower's passage);
the helix, the pair, the cell holonomy and the tube stay attached.

Consumers: the atlas row `hnn.tower-certified-section` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.CertifiedSection

open Finset

/-! ## 1. The release -/

/-- [definition] `x` released `b` coarser, to the nearest numerator, half away from zero
(`hnn::keyed_modes::release`): `(x + 2^(b−1)) ≫ b` for `x ≥ 0`, its mirror below zero. -/
def release (x : ℤ) (b : ℕ) : ℤ :=
  if b = 0 then x
  else if 0 ≤ x then (x + 2 ^ (b - 1)) / 2 ^ b else -((-x + 2 ^ (b - 1)) / 2 ^ b)

theorem two_pow_eq {b : ℕ} (hb : b ≠ 0) : (2 : ℤ) ^ b = 2 * 2 ^ (b - 1) := by
  cases b with
  | zero => exact absurd rfl hb
  | succ k => rw [Nat.add_sub_cancel, pow_succ']

theorem release_of_ne {b : ℕ} (hb : b ≠ 0) (x : ℤ) :
    release x b = if 0 ≤ x then (x + 2 ^ (b - 1)) / (2 * 2 ^ (b - 1))
      else -((-x + 2 ^ (b - 1)) / (2 * 2 ^ (b - 1))) := by
  rw [release, if_neg hb, two_pow_eq hb]

theorem ediv_bounds (a d : ℤ) (hd : 0 < d) : d * (a / d) ≤ a ∧ a < d * (a / d) + d := by
  have h1 := Int.mul_ediv_add_emod a d
  have h2 := Int.emod_nonneg a hd.ne'
  have h3 := Int.emod_lt_of_pos a hd
  constructor <;> linarith

theorem halfUp_le {x p : ℤ} (hx : 0 ≤ x) (hp : 1 ≤ p) : (x + p) / (2 * p) ≤ x := by
  have h := (ediv_bounds (x + p) (2 * p) (by linarith)).1
  by_contra hq
  push Not at hq
  have h1 : 2 * p * (x + 1) ≤ 2 * p * ((x + p) / (2 * p)) :=
    mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 hq) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hp hx]

theorem halfUp_eq_zero {x p : ℤ} (hx : 0 ≤ x) (hxp : x < p) : (x + p) / (2 * p) = 0 :=
  Int.ediv_eq_zero_of_lt (by linarith) (by linarith)

/-- [proved-derived; formal-checked] Nothing released is nothing. -/
theorem release_zero (b : ℕ) : release 0 b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [release, if_pos rfl]
  have hp : (1 : ℤ) ≤ 2 ^ (b - 1) := one_le_pow₀ (by norm_num)
  rw [release_of_ne hb, if_pos le_rfl, zero_add]
  exact Int.ediv_eq_zero_of_lt (by linarith) (by linarith)

/-- [proved-derived; formal-checked] The release is odd: half away from zero on both sides. -/
theorem release_neg (x : ℤ) (b : ℕ) : release (-x) b = -release x b := by
  by_cases hb : b = 0
  · subst hb
    simp [release]
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [release_of_ne hb, release_of_ne hb, if_pos (by linarith : (0 : ℤ) ≤ -x),
      if_neg (not_le.2 h), neg_neg]
  · rw [neg_zero, release_zero, neg_zero]
  · rw [release_of_ne hb, release_of_ne hb, if_neg (not_le.2 (by linarith : -x < 0)),
      if_pos h.le, neg_neg]

/-- [proved-derived; formal-checked] Released, a nonnegative value stays between zero and itself. -/
theorem release_bounds_of_nonneg {x : ℤ} {b : ℕ} (hx : 0 ≤ x) :
    0 ≤ release x b ∧ release x b ≤ x := by
  by_cases hb : b = 0
  · subst hb
    rw [release, if_pos rfl]
    exact ⟨hx, le_rfl⟩
  have hp : (1 : ℤ) ≤ 2 ^ (b - 1) := one_le_pow₀ (by norm_num)
  rw [release_of_ne hb, if_pos hx]
  exact ⟨Int.ediv_nonneg (by linarith) (by linarith), halfUp_le hx hp⟩

/-- [proved-derived; formal-checked] Released, a nonpositive value stays between itself and zero. -/
theorem release_bounds_of_nonpos {x : ℤ} {b : ℕ} (hx : x ≤ 0) :
    x ≤ release x b ∧ release x b ≤ 0 := by
  obtain ⟨h0, h1⟩ := release_bounds_of_nonneg (b := b) (neg_nonneg.2 hx)
  rw [release_neg] at h0 h1
  constructor <;> linarith

theorem release_eq_zero_of_nonneg {x : ℤ} {b : ℕ} (hx : 0 ≤ x) (h : 2 * x < 2 ^ b) :
    release x b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [pow_zero] at h
    have hx0 : x = 0 := by omega
    subst hx0
    exact release_zero 0
  rw [release_of_ne hb, if_pos hx]
  rw [two_pow_eq hb] at h
  exact halfUp_eq_zero hx (by linarith)

/-- [proved-derived; formal-checked] A value below half a coarse grain releases to zero. -/
theorem release_eq_zero {x : ℤ} {b : ℕ} (h : 2 * |x| < 2 ^ b) : release x b = 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h
    exact release_eq_zero_of_nonneg hx h
  · rw [abs_of_neg hx] at h
    have hx' : 0 ≤ -x := by linarith
    rw [← neg_neg x, release_neg, release_eq_zero_of_nonneg hx' h, neg_zero]

theorem release_eq_zero_of_natAbs {x : ℤ} {b : ℕ} (h : 2 * x.natAbs < b) : release x b = 0 := by
  apply release_eq_zero
  have h1 : 2 * x.natAbs < 2 ^ b := lt_trans h b.lt_two_pow_self
  have h2 : ((2 * x.natAbs : ℕ) : ℤ) < ((2 ^ b : ℕ) : ℤ) := Nat.cast_lt.2 h1
  rw [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs] at h2
  exact_mod_cast h2

/-- [proved-derived; formal-checked] **The halving ends**: every finite family of step entries
releases to zero after finitely many halvings, and stays released. -/
theorem halving_ends {ι : Type*} (s : Finset ι) (x : ι → ℤ) :
    ∃ b₀ : ℕ, ∀ b, b₀ ≤ b → ∀ i ∈ s, release (x i) b = 0 := by
  refine ⟨s.sup (fun i => 2 * (x i).natAbs + 1), fun b hb i hi => release_eq_zero_of_natAbs ?_⟩
  have h : 2 * (x i).natAbs + 1 ≤ s.sup (fun i => 2 * (x i).natAbs + 1) :=
    Finset.le_sup (f := fun i => 2 * (x i).natAbs + 1) hi
  omega

/-! ## 2. The moment law -/

/-- [definition] A moment moved toward its input at rate `2^(−r)`: `m + release(g − m, r)`, and
one grain toward `g` when that release is zero (`hnn::tower::toward`). -/
def toward (m g : ℤ) (r : ℕ) : ℤ :=
  m + if release (g - m) r = 0 then Int.sign (g - m) else release (g - m) r

/-- [proved-derived; formal-checked] At its input the moment stays. -/
theorem toward_self (g : ℤ) (r : ℕ) : toward g g r = g := by
  simp [toward, release_zero]

/-- [proved-derived; formal-checked] Below its input the moment moves up, never past it. -/
theorem toward_of_lt {m g : ℤ} (r : ℕ) (h : m < g) : m < toward m g r ∧ toward m g r ≤ g := by
  have hd : 0 ≤ g - m := by linarith
  obtain ⟨h0, h1⟩ := release_bounds_of_nonneg (b := r) hd
  have hs : Int.sign (g - m) = 1 := Int.sign_eq_one_of_pos (by linarith)
  unfold toward
  split_ifs with hz
  · rw [hs]
    constructor <;> linarith [Int.add_one_le_iff.2 h]
  · have hpos : 0 < release (g - m) r := lt_of_le_of_ne h0 (Ne.symm hz)
    constructor <;> linarith

/-- [proved-derived; formal-checked] Above its input the moment moves down, never past it. -/
theorem toward_of_gt {m g : ℤ} (r : ℕ) (h : g < m) : g ≤ toward m g r ∧ toward m g r < m := by
  have hd : g - m ≤ 0 := by linarith
  obtain ⟨h0, h1⟩ := release_bounds_of_nonpos (b := r) hd
  have hs : Int.sign (g - m) = -1 := Int.sign_eq_neg_one_of_neg (by linarith)
  unfold toward
  split_ifs with hz
  · rw [hs]
    constructor <;> linarith [Int.add_one_le_iff.2 h]
  · have hneg : release (g - m) r < 0 := lt_of_le_of_ne h1 hz
    constructor <;> linarith

/-- [proved-derived; formal-checked] **The moment reaches a constant input exactly**: from `m`,
the input `g` held for `k ≥ |g − m|` sections leaves the moment at `g`. -/
theorem toward_iterate (g : ℤ) (r : ℕ) :
    ∀ (k : ℕ) (m : ℤ), |g - m| ≤ k → (fun m => toward m g r)^[k] m = g := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have h0 : |g - m| ≤ 0 := by exact_mod_cast hm
    have h1 : g - m = 0 := abs_nonpos_iff.1 h0
    rw [Function.iterate_zero_apply]
    linarith
  | succ k ih =>
    intro m hm
    rw [Function.iterate_succ_apply]
    apply ih
    show |g - toward m g r| ≤ (k : ℤ)
    push_cast at hm
    rcases lt_trichotomy m g with h | h | h
    · obtain ⟨h1, h2⟩ := toward_of_lt r h
      have e1 : |g - m| = g - m := abs_of_nonneg (by linarith)
      have e2 : |g - toward m g r| = g - toward m g r := abs_of_nonneg (by linarith)
      have h3 := Int.add_one_le_iff.2 h1
      rw [e1] at hm
      rw [e2]
      linarith
    · subst h
      rw [toward_self, sub_self, abs_zero]
      exact_mod_cast Nat.zero_le k
    · obtain ⟨h1, h2⟩ := toward_of_gt r h
      have e1 : |g - m| = -(g - m) := abs_of_neg (by linarith)
      have e2 : |g - toward m g r| = -(g - toward m g r) := abs_of_nonpos (by linarith)
      have h3 := Int.add_one_le_iff.2 h2
      rw [e1] at hm
      rw [e2]
      linarith

/-- [proved-derived; formal-checked] A silent contact's moment (its covector, and so its square,
zero every section) reaches zero within `|m|` sections and stays there. -/
theorem silent_moment_reaches_zero (r : ℕ) (m : ℤ) (k : ℕ) (hk : |m| ≤ k) :
    (fun m => toward m 0 r)^[k] m = 0 :=
  toward_iterate 0 r k m (by rwa [zero_sub, abs_neg])

/-- [definition] The deposit's step for one entry (`hnn::tower::deposit_step`):
`((m ≪ grain) ≫ rate) / (⌊√v⌋ + 1)`, the last division truncating. -/
def depositStep (m v : ℤ) (grain rate : ℕ) : ℤ :=
  Int.tdiv (m * 2 ^ grain / 2 ^ rate) ((v.toNat.sqrt : ℤ) + 1)

/-- [proved-derived; formal-checked] A zero first moment steps nothing. -/
theorem depositStep_zero (v : ℤ) (grain rate : ℕ) : depositStep 0 v grain rate = 0 := by
  simp [depositStep, Int.zero_tdiv]

/-- [proved-derived; formal-checked] **A silent contact's step reaches zero**: once its first
moment has had `|m|` silent sections, its step is zero whatever its second moment is. -/
theorem silent_step_reaches_zero (r grain rate : ℕ) (m v : ℤ) (k : ℕ) (hk : |m| ≤ k) :
    depositStep ((fun m => toward m 0 r)^[k] m) v grain rate = 0 := by
  rw [silent_moment_reaches_zero r m k hk, depositStep_zero]

/-! ## 3. The exact certificate is the code's strict fall -/

/-- [definition] A section's code in bits: `Σ_i −log₂ (m_i/t_i)` over its faces' masses and totals. -/
noncomputable def code {a : ℕ} (m t : Fin a → ℕ) : ℝ :=
  ∑ i, (Real.logb 2 (t i) - Real.logb 2 (m i))

/-- [definition] The exact comparison (`hnn::tower::fewer_bits_exact`):
`Π m_new · Π t_old > Π m_old · Π t_new`. -/
def fewerBitsExact {a b : ℕ} (m₀ t₀ : Fin a → ℕ) (m₁ t₁ : Fin b → ℕ) : Prop :=
  (∏ i, m₀ i) * (∏ i, t₁ i) < (∏ i, m₁ i) * (∏ i, t₀ i)

theorem code_eq {a : ℕ} {m t : Fin a → ℕ} (hm : ∀ i, 0 < m i) (ht : ∀ i, 0 < t i) :
    code m t = (Real.log ((∏ i, t i : ℕ) : ℝ) - Real.log ((∏ i, m i : ℕ) : ℝ)) / Real.log 2 := by
  have ht' : ∀ i ∈ (Finset.univ : Finset (Fin a)), ((t i : ℕ) : ℝ) ≠ 0 :=
    fun i _ => Nat.cast_ne_zero.2 (ht i).ne'
  have hm' : ∀ i ∈ (Finset.univ : Finset (Fin a)), ((m i : ℕ) : ℝ) ≠ 0 :=
    fun i _ => Nat.cast_ne_zero.2 (hm i).ne'
  rw [Nat.cast_prod, Nat.cast_prod, Real.log_prod ht', Real.log_prod hm',
    ← Finset.sum_sub_distrib, Finset.sum_div]
  simp only [code, Real.logb, sub_div]

theorem cast_prod_pos {c : ℕ} (f : Fin c → ℕ) (hf : ∀ i, 0 < f i) :
    (0 : ℝ) < ((∏ i, f i : ℕ) : ℝ) :=
  Nat.cast_pos.2 (Finset.prod_pos fun i _ => hf i)

/-- [proved-derived; formal-checked] **The exact certificate is the code's strict fall**: with
positive masses and totals, the products compare as the codes do. -/
theorem fewerBitsExact_iff {a b : ℕ} {m₀ t₀ : Fin a → ℕ} {m₁ t₁ : Fin b → ℕ}
    (hm₀ : ∀ i, 0 < m₀ i) (ht₀ : ∀ i, 0 < t₀ i) (hm₁ : ∀ i, 0 < m₁ i) (ht₁ : ∀ i, 0 < t₁ i) :
    fewerBitsExact m₀ t₀ m₁ t₁ ↔ code m₁ t₁ < code m₀ t₀ := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have pm₀ := cast_prod_pos m₀ hm₀
  have pt₀ := cast_prod_pos t₀ ht₀
  have pm₁ := cast_prod_pos m₁ hm₁
  have pt₁ := cast_prod_pos t₁ ht₁
  have key : fewerBitsExact m₀ t₀ m₁ t₁ ↔
      ((∏ i, m₀ i : ℕ) : ℝ) * ((∏ i, t₁ i : ℕ) : ℝ) <
        ((∏ i, m₁ i : ℕ) : ℝ) * ((∏ i, t₀ i : ℕ) : ℝ) := by
    rw [fewerBitsExact, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_lt]
  rw [key, code_eq hm₁ ht₁, code_eq hm₀ ht₀, div_lt_div_iff_of_pos_right hl,
    ← Real.log_lt_log_iff (mul_pos pm₀ pt₁) (mul_pos pm₁ pt₀),
    Real.log_mul pm₀.ne' pt₁.ne', Real.log_mul pm₁.ne' pt₀.ne']
  constructor <;> intro h <;> linarith

/-! ## 4. The partition decides as the products do -/

/-- [definition] A side's summed reading `Σ_i (ρ(m_i) − ρ(t_i))`. -/
def side {a : ℕ} (ρ : ℕ → ℤ) (m t : Fin a → ℕ) : ℤ :=
  ∑ i, (ρ (m i) - ρ (t i))

/-- [proved-derived; formal-checked] A side's summed reading lies within `2 s` a face of `−G`
times its code, for a reading within `s` of `G log₂`. -/
theorem side_close {a : ℕ} {ρ : ℕ → ℤ} {G s : ℝ}
    (hρ : ∀ v, 0 < v → |(ρ v : ℝ) - G * Real.logb 2 v| ≤ s)
    {m t : Fin a → ℕ} (hm : ∀ i, 0 < m i) (ht : ∀ i, 0 < t i) :
    |(side ρ m t : ℝ) + G * code m t| ≤ s * 2 * a := by
  have h : (side ρ m t : ℝ) + G * code m t =
      ∑ i, (((ρ (m i) : ℝ) - G * Real.logb 2 (m i)) -
        ((ρ (t i) : ℝ) - G * Real.logb 2 (t i))) := by
    rw [side, code, Int.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |((ρ (m i) : ℝ) - G * Real.logb 2 (m i)) - ((ρ (t i) : ℝ) - G * Real.logb 2 (t i))|
      ≤ ∑ _i : Fin a, s * 2 := Finset.sum_le_sum fun i _ => by
        have h1 := abs_le.1 (hρ (m i) (hm i))
        have h2 := abs_le.1 (hρ (t i) (ht i))
        exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    _ = s * 2 * a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- [proved-derived; formal-checked] Readings past every slack together decide "fewer". -/
theorem readings_decide_fewer {a b : ℕ} {ρ : ℕ → ℤ} {G s : ℝ} (hG : 0 < G)
    (hρ : ∀ v, 0 < v → |(ρ v : ℝ) - G * Real.logb 2 v| ≤ s)
    {m₀ t₀ : Fin a → ℕ} {m₁ t₁ : Fin b → ℕ}
    (hm₀ : ∀ i, 0 < m₀ i) (ht₀ : ∀ i, 0 < t₀ i) (hm₁ : ∀ i, 0 < m₁ i) (ht₁ : ∀ i, 0 < t₁ i)
    (h : s * 2 * (a + b) < (side ρ m₁ t₁ - side ρ m₀ t₀ : ℝ)) :
    fewerBitsExact m₀ t₀ m₁ t₁ := by
  rw [fewerBitsExact_iff hm₀ ht₀ hm₁ ht₁]
  have h1 := abs_le.1 (side_close hρ hm₀ ht₀)
  have h2 := abs_le.1 (side_close hρ hm₁ ht₁)
  have h3 : G * code m₁ t₁ < G * code m₀ t₀ := by
    linarith [h1.1, h1.2, h2.1, h2.2]
  exact lt_of_mul_lt_mul_left h3 hG.le

/-- [proved-derived; formal-checked] Readings below every slack together decide "not fewer". -/
theorem readings_decide_not_fewer {a b : ℕ} {ρ : ℕ → ℤ} {G s : ℝ} (hG : 0 < G)
    (hρ : ∀ v, 0 < v → |(ρ v : ℝ) - G * Real.logb 2 v| ≤ s)
    {m₀ t₀ : Fin a → ℕ} {m₁ t₁ : Fin b → ℕ}
    (hm₀ : ∀ i, 0 < m₀ i) (ht₀ : ∀ i, 0 < t₀ i) (hm₁ : ∀ i, 0 < m₁ i) (ht₁ : ∀ i, 0 < t₁ i)
    (h : (side ρ m₁ t₁ - side ρ m₀ t₀ : ℝ) < -(s * 2 * (a + b))) :
    ¬ fewerBitsExact m₀ t₀ m₁ t₁ := by
  rw [fewerBitsExact_iff hm₀ ht₀ hm₁ ht₁, not_lt]
  have h1 := abs_le.1 (side_close hρ hm₀ ht₀)
  have h2 := abs_le.1 (side_close hρ hm₁ ht₁)
  have h3 : G * code m₀ t₀ < G * code m₁ t₁ := by
    linarith [h1.1, h1.2, h2.1, h2.2]
  exact (lt_of_mul_lt_mul_left h3 hG.le).le

/-- [definition] **The certificate decided by partition** (`hnn::tower::fewer_bits`): a zero mass or
total goes to the products; otherwise the summed readings decide outside the band
`slack · 2 · (a + b)`, and the products inside it. -/
def fewerBits {a b : ℕ} (ρ : ℕ → ℤ) (slack : ℤ) (m₀ t₀ : Fin a → ℕ) (m₁ t₁ : Fin b → ℕ) :
    Prop :=
  if (∃ i, m₀ i = 0 ∨ t₀ i = 0) ∨ (∃ i, m₁ i = 0 ∨ t₁ i = 0) then fewerBitsExact m₀ t₀ m₁ t₁
  else if slack * 2 * (a + b) < side ρ m₁ t₁ - side ρ m₀ t₀ then True
  else if side ρ m₁ t₁ - side ρ m₀ t₀ < -(slack * 2 * (a + b)) then False
  else fewerBitsExact m₀ t₀ m₁ t₁

/-- [proved-derived; formal-checked] **The partition decides as the products do**, in every case,
for any reading within the slack of `G log₂`. -/
theorem fewerBits_iff {a b : ℕ} {ρ : ℕ → ℤ} {G : ℝ} {slack : ℤ} (hG : 0 < G)
    (hρ : ∀ v, 0 < v → |(ρ v : ℝ) - G * Real.logb 2 v| ≤ slack)
    (m₀ t₀ : Fin a → ℕ) (m₁ t₁ : Fin b → ℕ) :
    fewerBits ρ slack m₀ t₀ m₁ t₁ ↔ fewerBitsExact m₀ t₀ m₁ t₁ := by
  unfold fewerBits
  split_ifs with hz h1 h2
  · exact Iff.rfl
  · simp only [not_or, not_exists] at hz
    refine ⟨fun _ => readings_decide_fewer hG hρ (fun i => Nat.pos_of_ne_zero (hz.1 i).1)
      (fun i => Nat.pos_of_ne_zero (hz.1 i).2) (fun i => Nat.pos_of_ne_zero (hz.2 i).1)
      (fun i => Nat.pos_of_ne_zero (hz.2 i).2) ?_, fun _ => trivial⟩
    have h1' : ((slack * 2 * (a + b) : ℤ) : ℝ) < ((side ρ m₁ t₁ - side ρ m₀ t₀ : ℤ) : ℝ) :=
      Int.cast_lt.2 h1
    push_cast at h1'
    linarith
  · simp only [not_or, not_exists] at hz
    refine ⟨False.elim, fun hf => readings_decide_not_fewer hG hρ
      (fun i => Nat.pos_of_ne_zero (hz.1 i).1) (fun i => Nat.pos_of_ne_zero (hz.1 i).2)
      (fun i => Nat.pos_of_ne_zero (hz.2 i).1) (fun i => Nat.pos_of_ne_zero (hz.2 i).2) ?_ hf⟩
    have h2' : ((side ρ m₁ t₁ - side ρ m₀ t₀ : ℤ) : ℝ) < ((-(slack * 2 * (a + b)) : ℤ) : ℝ) :=
      Int.cast_lt.2 h2
    push_cast at h2'
    linarith
  · exact Iff.rfl

/-- [proved-derived; formal-checked] **A certified step strictly lowers the section's code.** -/
theorem certified_lowers_code {a b : ℕ} {ρ : ℕ → ℤ} {G : ℝ} {slack : ℤ} (hG : 0 < G)
    (hρ : ∀ v, 0 < v → |(ρ v : ℝ) - G * Real.logb 2 v| ≤ slack)
    {m₀ t₀ : Fin a → ℕ} {m₁ t₁ : Fin b → ℕ}
    (hm₀ : ∀ i, 0 < m₀ i) (ht₀ : ∀ i, 0 < t₀ i) (hm₁ : ∀ i, 0 < m₁ i) (ht₁ : ∀ i, 0 < t₁ i)
    (hc : fewerBits ρ slack m₀ t₀ m₁ t₁) : code m₁ t₁ < code m₀ t₀ :=
  (fewerBitsExact_iff hm₀ ht₀ hm₁ ht₁).1 ((fewerBits_iff hG hρ m₀ t₀ m₁ t₁).1 hc)

/-! ## 5. The section -/

/-- [definition] Whether the step, released `h` coarser, still moves an entry. -/
def moves {n : ℕ} (step : Fin n → ℤ) (h : ℕ) : Prop :=
  ∃ i, release (step i) h ≠ 0

/-- [proved-derived; formal-checked] Halving long enough, nothing moves. -/
theorem halving_stops {n : ℕ} (step : Fin n → ℤ) : ∃ h, ¬ moves step h := by
  obtain ⟨b₀, hb⟩ := halving_ends Finset.univ step
  refine ⟨b₀, fun hm => ?_⟩
  obtain ⟨i, hi⟩ := hm
  exact hi (hb b₀ le_rfl i (Finset.mem_univ i))

/-- [proved-derived; formal-checked] **The section's deposit**: halving from the proposed step,
the section stops at the first count of halvings at which nothing moves or the certificate holds;
it does stop, and when it deposits the step is certified and the reread code is strictly below the
opening's (`cert h` the certificate at `h` halvings, `codeAt h` the reread code, `code₀` the
opening's). -/
theorem section_deposit {n : ℕ} (step : Fin n → ℤ) (cert : ℕ → Prop) (codeAt : ℕ → ℝ)
    (code₀ : ℝ) (hcert : ∀ h, moves step h → cert h → codeAt h < code₀) :
    ∃ h, (∀ k < h, moves step k ∧ ¬ cert k) ∧
      (¬ moves step h ∨ (moves step h ∧ cert h ∧ codeAt h < code₀)) := by
  classical
  have hP : ∃ h, ¬ moves step h ∨ cert h := (halving_stops step).imp fun _ h => Or.inl h
  refine ⟨Nat.find hP, fun k hk => ?_, ?_⟩
  · have h := not_or.1 (Nat.find_min hP hk)
    exact ⟨not_not.1 h.1, h.2⟩
  · rcases Nat.find_spec hP with h | h
    · exact Or.inl h
    · by_cases hm : moves step (Nat.find hP)
      · exact Or.inr ⟨hm, h, hcert _ hm h⟩
      · exact Or.inl hm

end Holonics.HNN.CertifiedSection
