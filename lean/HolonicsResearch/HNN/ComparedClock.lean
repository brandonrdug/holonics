import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# A clock is a comparison: counts survive every retiming, a count lasts as long as its store rings, and one fade reads no gap

The record `research/records/2026-11-24_CONTEXT_IS_A_CALENDAR_A_RECEIVER_READS_COUNTS_OF_ONE_CYCLE_AGAINST_ANOTHER_A_COUNT_LASTS_AS_LONG_AS_ITS_STORE_RINGS_ONE_FADE_READS_NO_GAP_AND_TWO_READ_IT_AND_HER_RINGS_FADE_BEFORE_THEY_TURN.md`
states the law this file's statements stand under: a receiver reads no time, it reads counts of one
cycle against another; a unit is attained only by such a comparison, and it is kept only as long as
the store that counts it rings. `Holonics.Aeon.Clock` holds the reading as windings and an open
phase, the carry word and the lock at an address. This file adds what a comparison survives, what it
attains, what a fading store can and cannot read of a silent gap, what a count asks of a store's
quality, how an uncompared clock errs, and the cone that local ticks draw.

A cycle is given by its ticks, `a : ℕ → ℝ`, the hidden axis's values at which it crosses its
section; no statement here reads those values.

[proved-derived; formal-checked] What is proved.

1. **A count survives every retiming** (`countBefore_retimed`): the count of one cycle's ticks that
   stand at or before a tick of another is the same after any strictly increasing change of the
   hidden axis. What a receiver can read of two cycles is such counts.
2. **A comparison of `N` windings attains a ratio within `1/N`** (`ratio_within`): with `c` the
   count of whole turns of a cycle of rate `x` in `N` turns of the unit, `c/N ≤ x < (c + 1)/N`.
3. **One fade reads no gap** (`one_fade_reads_no_gap`): a store fading by `a` a step that reads
   `A aˢ` after `s` silent steps reads the same from another start after any other count `t`. An
   amplitude and an age trade.
4. **Two unlike fades read it** (`two_fades_ratio`, `two_fades_read_gap`): the ratio of two stores
   fading by `a < b` from one start is `(a/b)ᵗ`, free of the start, and it fixes `t`.
5. **A count asks for quality** (`turns_under_grain`, `skin_turn`, `skin_turn_lt`): a store that
   keeps at most a grain `g` of itself over one turn keeps at most `g` over any count of turns, so
   it counts none above that grain; a ring of period `n` fading `e^(−2π/n)` a step, one e-fold a
   radian, keeps `e^(−2π) < 1/400` over one turn of itself, whatever its period.
6. **An uncompared clock errs by the count** (`dead_reckoning`, `dead_reckoning_attained`): a clock
   whose stride errs by at most `ε` a step errs by at most `n ε` after `n` steps, and a constant
   error attains it: no bound stands that the count does not enter.
7. **Local ticks draw a cone** (`Local.comp`, `Local.iterate`, `outside_cone_moves_nothing`): a tick
   that reads a site's neighbours within `r` gives, after `k` ticks, a state fixed by the sites
   within `k r`; nothing outside that cone moves it.
8. **A rate held with no count costs its binary entropy** (`rateCode`, `log_lt_rateCode`,
   `rateCode_lt_one_add_log`): a reader that holds how often a cycle ticks, once in `P` places, and
   not where in its period it stands, pays `log P` at each tick and `log (P/(P − 1))` at each other
   place, between `log P` and `1 + log P` a period. A reader that holds the count pays nothing once
   the period stands, so this is what a count is worth on a kept period.

Not proved here: the general relation between a resonance's quality and the fineness of a
comparison it can hold (the line width; from the literature), and Kelvin's and Helmholtz's theorems
for an ideal fluid, which the record cites.

The computational object is the helical pair interaction read along a strand's clock: a contact
compares two sites' turns. Of the winding guide's six general objects this touches the helix (a
cycle and its carry), the pair (a comparison of two cycles) and the tower thread (a count carried up
a level); faces and placement, the cell holonomy and the tube stay attached.

Consumers: the atlas rows `aeon.count-survives-every-retiming`, `aeon.one-fade-reads-no-gap`,
`aeon.count-asks-for-quality`, `aeon.uncompared-clock-errs-by-the-count`,
`aeon.rate-without-count-costs-its-entropy`, `tower.local-ticks-draw-a-cone` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ComparedClock

open Finset

variable {α β γ : Type*}

/-- The count, among the first `M` ticks of cycle `a`, of those that stand at or before the `n`-th
tick of cycle `b`. -/
noncomputable def countBefore (a b : ℕ → ℝ) (n M : ℕ) : ℕ :=
  ((range M).filter (fun k => a k ≤ b n)).card

/-- **A count survives every retiming.** Under any strictly increasing change `σ` of the hidden
axis, the count of one cycle's ticks at or before another's tick is the same. -/
theorem countBefore_retimed {σ : ℝ → ℝ} (hσ : StrictMono σ) (a b : ℕ → ℝ) (n M : ℕ) :
    countBefore (fun k => σ (a k)) (fun k => σ (b k)) n M = countBefore a b n M := by
  unfold countBefore
  have h : (range M).filter (fun k => σ (a k) ≤ σ (b n)) =
      (range M).filter (fun k => a k ≤ b n) :=
    Finset.filter_congr (fun k _ => hσ.le_iff_le)
  rw [h]

/-- **A comparison of `N` windings attains a ratio within `1/N`.** With `c = ⌊N x⌋` the count of
whole turns of a cycle of rate `x ≥ 0` in `N` turns of the unit, `c/N ≤ x < (c + 1)/N`. -/
theorem ratio_within {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : 0 < N) :
    (⌊(N : ℝ) * x⌋₊ : ℝ) / N ≤ x ∧ x < ((⌊(N : ℝ) * x⌋₊ : ℝ) + 1) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ (N : ℝ) * x := mul_nonneg hN'.le hx
  have hle : (⌊(N : ℝ) * x⌋₊ : ℝ) ≤ N * x := Nat.floor_le h0
  have hlt : (N : ℝ) * x < ⌊(N : ℝ) * x⌋₊ + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [div_le_iff₀ hN']
    linarith
  · rw [lt_div_iff₀ hN']
    linarith

/-- **One fade reads no gap.** A store fading by `a` a step reads `A aˢ` after `s` silent steps;
another start `A'` gives the same reading after any other count `t`. -/
theorem one_fade_reads_no_gap {a A : ℝ} (ha : 0 < a) (hA : 0 < A) (s t : ℕ) :
    ∃ A' : ℝ, 0 < A' ∧ A' * a ^ t = A * a ^ s := by
  refine ⟨A * a ^ s / a ^ t, by positivity, ?_⟩
  exact div_mul_cancel₀ _ (pow_pos ha t).ne'

/-- The ratio of two stores fading by `a` and by `b` from one start `A` is `(a/b)ᵗ`: the start
leaves it. -/
theorem two_fades_ratio {a b A : ℝ} (hA : A ≠ 0) (t : ℕ) :
    (A * a ^ t) / (A * b ^ t) = (a / b) ^ t := by
  rw [mul_div_mul_left _ _ hA, div_pow]

/-- **Two unlike fades read the gap.** With `0 < a < b` the ratio `(a/b)ᵗ` fixes `t`. -/
theorem two_fades_read_gap {a b : ℝ} (ha : 0 < a) (hab : a < b) {s t : ℕ}
    (h : (a / b) ^ s = (a / b) ^ t) : s = t := by
  have hb : 0 < b := ha.trans hab
  have h0 : 0 < a / b := div_pos ha hb
  have h1 : a / b < 1 := (div_lt_one hb).mpr hab
  exact pow_right_injective₀ h0 h1.ne h

/-- **A count asks for quality.** A store that keeps at most a grain `g ≤ 1` of itself over one turn
keeps at most `g` over any count of turns from one up. -/
theorem turns_under_grain {r g : ℝ} (hr : 0 ≤ r) (hrg : r ≤ g) (hg : g ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    r ^ k ≤ g := by
  calc r ^ k ≤ r ^ 1 := pow_le_pow_of_le_one hr (hrg.trans hg) hk
    _ = r := pow_one r
    _ ≤ g := hrg

/-- A ring of period `n` that fades `e^(−2π/n)` a step, one e-fold a radian of its turn, keeps
`e^(−2π)` over one turn of itself, whatever its period. -/
theorem skin_turn {n : ℕ} (hn : 0 < n) :
    Real.exp (-(2 * Real.pi) / n) ^ n = Real.exp (-(2 * Real.pi)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp

/-- **A ring fading one e-fold a radian counts no turn.** `e^(−2π) < 1/400`. -/
theorem skin_turn_lt : Real.exp (-(2 * Real.pi)) < 1 / 400 := by
  have hpi : (6 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hexp : Real.exp (-(2 * Real.pi)) < Real.exp (-6) := Real.exp_lt_exp.mpr (by linarith)
  have h1 : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h400 : (400 : ℝ) < Real.exp 6 := by
    rw [h6]
    calc (400 : ℝ) < 2.718 ^ 6 := by norm_num
      _ < Real.exp 1 ^ 6 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  calc Real.exp (-(2 * Real.pi)) < Real.exp (-6) := hexp
    _ = (Real.exp 6)⁻¹ := Real.exp_neg 6
    _ < (400 : ℝ)⁻¹ := (inv_lt_inv₀ (Real.exp_pos 6) (by norm_num)).mpr h400
    _ = 1 / 400 := by norm_num

/-- **An uncompared clock errs by the count.** A clock whose stride `κ'` errs from `κ` by at most
`ε` a step errs by at most `n ε` after `n` steps. -/
theorem dead_reckoning (κ κ' : ℕ → ℝ) (ε : ℝ) (h : ∀ k, |κ' k - κ k| ≤ ε) (n : ℕ) :
    |∑ k ∈ range n, κ' k - ∑ k ∈ range n, κ k| ≤ n * ε := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ k ∈ range n, (κ' k - κ k)| ≤ ∑ k ∈ range n, |κ' k - κ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range n, ε := Finset.sum_le_sum (fun k _ => h k)
    _ = n * ε := by simp

/-- The bound is attained: a constant error of `ε` a step is `n ε` after `n` steps. -/
theorem dead_reckoning_attained (κ : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (κ k + ε) - ∑ k ∈ range n, κ k = n * ε := by
  rw [Finset.sum_add_distrib]
  simp

/-- The code, in nats, that one period of `P` places with one tick costs a reader that holds the
tick's rate `1/P` and no place in the period: `log P` at the tick and `log (P/(P − 1))` at each of
the other `P − 1` places, `P` times the binary entropy of `1/P`. -/
noncomputable def rateCode (P : ℝ) : ℝ :=
  Real.log P + (P - 1) * Real.log (P / (P - 1))

/-- **A rate held with no count costs more than `log P` a period**: the tick's own code, and
something at every other place. A reader that holds the count pays nothing. -/
theorem log_lt_rateCode {P : ℝ} (hP : 1 < P) : Real.log P < rateCode P := by
  have h2 : 0 < P - 1 := by linarith
  have h3 : 1 < P / (P - 1) := by
    rw [lt_div_iff₀ h2]
    linarith
  have h4 : 0 < Real.log (P / (P - 1)) := Real.log_pos h3
  have h5 : 0 < (P - 1) * Real.log (P / (P - 1)) := mul_pos h2 h4
  unfold rateCode
  linarith

/-- **And less than `1 + log P`**: the places between two ticks cost under one nat together,
whatever the period. -/
theorem rateCode_lt_one_add_log {P : ℝ} (hP : 1 < P) : rateCode P < 1 + Real.log P := by
  have h2 : 0 < P - 1 := by linarith
  have h3 : 0 < P / (P - 1) := div_pos (by linarith) h2
  have hne : P / (P - 1) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq h2.ne'] at h
    linarith
  have h5 : Real.log (P / (P - 1)) < P / (P - 1) - 1 := Real.log_lt_sub_one_of_pos h3 hne
  have h6 : (P - 1) * (P / (P - 1) - 1) = 1 := by
    field_simp
    ring
  have h7 : (P - 1) * Real.log (P / (P - 1)) < (P - 1) * (P / (P - 1) - 1) :=
    mul_lt_mul_of_pos_left h5 h2
  unfold rateCode
  linarith

/-- A tick is local with reach `r`: the state it gives site `t` is fixed by the states of the sites
within `r` of `t`. -/
def Local (r : ℕ) (F : (ℤ → α) → ℤ → β) : Prop :=
  ∀ x y : ℤ → α, ∀ t : ℤ, (∀ i, |i - t| ≤ (r : ℤ) → x i = y i) → F x t = F y t

/-- A tick of reach `s` after a tick of reach `r` has reach `r + s`. -/
theorem Local.comp {F : (ℤ → α) → ℤ → β} {G : (ℤ → β) → ℤ → γ} {r s : ℕ}
    (hF : Local r F) (hG : Local s G) : Local (r + s) (fun x => G (F x)) := by
  intro x y t h
  apply hG
  intro j hj
  apply hF
  intro i hi
  apply h
  have h3 : |i - t| ≤ |i - j| + |j - t| := abs_sub_le i j t
  push_cast
  linarith

/-- **Local ticks draw a cone.** After `k` ticks of reach `r` a site's state is fixed by the sites
within `k r`. -/
theorem Local.iterate {F : (ℤ → α) → ℤ → α} {r : ℕ} (hF : Local r F) (k : ℕ) :
    Local (k * r) (F^[k]) := by
  induction k with
  | zero =>
    intro x y t h
    simpa using h t (by simp)
  | succ k ih =>
    intro x y t h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    apply ih
    intro j hj
    apply hF
    intro i hi
    apply h
    have h3 : |i - t| ≤ |i - j| + |j - t| := abs_sub_le i j t
    push_cast
    push_cast at hj
    nlinarith

/-- Nothing outside the cone moves a state: two passages that agree within `k r` of a site hold the
same state there after `k` ticks. -/
theorem outside_cone_moves_nothing {F : (ℤ → α) → ℤ → α} {r : ℕ} (hF : Local r F) (k : ℕ)
    (x y : ℤ → α) (t : ℤ) (h : ∀ i, |i - t| ≤ ((k * r : ℕ) : ℤ) → x i = y i) :
    F^[k] x t = F^[k] y t :=
  hF.iterate k x y t h

end Holonics.HNN.ComparedClock
