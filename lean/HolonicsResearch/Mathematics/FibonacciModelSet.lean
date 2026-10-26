import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-!
# The Fibonacci chain: inflation boosts the seen colour and contracts the hidden one

The record `research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md`
(atlas `quasi.fibonacci-model-set`) reads the Fibonacci quasicrystal as a model set: physical space
is one Galois colour of `ℤ[τ]`, the window lives in the conjugate, and inflation by the Pisot unit
`τ` boosts the seen colour and contracts the hidden one, so the hidden colour is held as a window,
never as a store. #410 owes it; this file proves the arithmetic of the two colours and of the
inflation `a ↦ ab`, `b ↦ a`, exactly (`τ = Real.goldenRatio`, `τ′ = Real.goldenConj`).

[proved-standard; formal-checked] What is proved.

1. **A power of a golden root is a Lucas–Fibonacci pair** (`lucas`, `two_mul_pow`,
   `goldenRatio_pow`, `goldenConj_pow`, `lucas_eq`): if `x² = x + 1` and `2x = 1 + s` then
   `2xⁿ = L_n + F_n s`, so `τⁿ = (L_n + F_n√5)/2`, `τ′ⁿ = (L_n − F_n√5)/2` and `L_n = τⁿ + τ′ⁿ`.
2. **The norm of `τⁿ` is `(−1)ⁿ`** (`lucas_sq_sub_five_fib_sq`): `L_n² − 5F_n² = 4(−1)ⁿ` in `ℤ`.
3. **The seen colour boosts and the hidden one contracts** (`abs_goldenConj_lt_one`,
   `seen_grows`, `hidden_shrinks`, `hidden_tendsto_zero`): `τⁿ⁺¹ > τⁿ`, `|τ′ⁿ⁺¹| < |τ′ⁿ|` and
   `τ′ⁿ → 0`.
4. **Inflation scales the chain by its root** (`inflate`, `gaps`, `gaps_inflate`,
   `gaps_iterate`): with the gap `a` read as a root `x` of `x² = x + 1` and `b` as `1`, inflation
   multiplies the total length by `x`, so the `n`-th inflation of `a` has length `xⁿ⁺¹`.
5. **The tiles count by Fibonacci** (`countA_inflate`, `countB_inflate`, `count_iterate`,
   `gaps_eq_count`, `tile_count`): the `n`-th inflation of `a` has `F_(n+1)` long and `F_n` short
   tiles, so `xⁿ⁺¹ = F_(n+1) x + F_n`.
6. **One word, two colours** (`seen_length`, `hidden_length`, `hidden_length_tendsto_zero`): the
   same inflated word measures `τⁿ⁺¹` in the seen colour and `τ′ⁿ⁺¹ → 0` in the hidden one.

Owed (#410): the window statement itself, that every vertex `m + nτ` of the chain has its
conjugate `m + nτ′` in `[−1, τ − 1)` and every such point of `ℤ[τ] ∩ [0, ∞)` is a vertex.

The computational object is the helical pair interaction: a tile is a pair of colours of one
element of `ℤ[τ]`, and inflation is the one move that turns the seen colour out and the hidden one
in. Of the winding guide's six general objects this touches the tower thread (inflation as a scale
level) and faces and placement (the window); the helix, the pair, the cell holonomy and the tube
stay attached.

Consumers: the atlas row `quasi.fibonacci-model-set`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.FibonacciModelSet

/-- [definition] The Lucas numbers `L_0 = 2`, `L_1 = 1`, `L_(n+2) = L_n + L_(n+1)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

/-- [proved-standard; formal-checked] The Lucas recurrence. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-- [proved-standard; formal-checked] **A power of a golden root is a Lucas–Fibonacci pair:** if
`x² = x + 1` and `2x = 1 + s`, then `2xⁿ = L_n + F_n s`. -/
theorem two_mul_pow {R : Type*} [CommRing R] (x s : R) (hx : x ^ 2 = x + 1) (hs : 2 * x = 1 + s)
    (n : ℕ) : 2 * x ^ n = (lucas n : R) + (Nat.fib n : R) * s := by
  have key : ∀ n, (2 * x ^ n = (lucas n : R) + (Nat.fib n : R) * s ∧
      2 * x ^ (n + 1) = (lucas (n + 1) : R) + (Nat.fib (n + 1) : R) * s) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [lucas]
      · simpa [lucas] using hs
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h2 : x ^ (n + 2) = x ^ (n + 1) + x ^ n := by
        rw [pow_add x n 2, hx]
        ring
      show 2 * x ^ (n + 2) = (lucas (n + 2) : R) + (Nat.fib (n + 2) : R) * s
      rw [h2, mul_add, ih.1, ih.2, lucas_add_two, Nat.fib_add_two]
      push_cast
      ring
  exact (key n).1

/-- [proved-standard; formal-checked] `τⁿ = (L_n + F_n√5)/2`. -/
theorem goldenRatio_pow (n : ℕ) :
    Real.goldenRatio ^ n = ((lucas n : ℝ) + (Nat.fib n : ℝ) * √5) / 2 := by
  have h := two_mul_pow Real.goldenRatio (√5) Real.goldenRatio_sq
    (show 2 * ((1 + √5) / 2) = 1 + √5 by ring) n
  linear_combination h / 2

/-- [proved-standard; formal-checked] `τ′ⁿ = (L_n − F_n√5)/2`. -/
theorem goldenConj_pow (n : ℕ) :
    Real.goldenConj ^ n = ((lucas n : ℝ) - (Nat.fib n : ℝ) * √5) / 2 := by
  have h := two_mul_pow Real.goldenConj (-√5) Real.goldenConj_sq
    (show 2 * ((1 - √5) / 2) = 1 + -√5 by ring) n
  linear_combination h / 2

/-- [proved-standard; formal-checked] **The Lucas number is the trace of `τⁿ`:**
`L_n = τⁿ + τ′ⁿ`. -/
theorem lucas_eq (n : ℕ) : (lucas n : ℝ) = Real.goldenRatio ^ n + Real.goldenConj ^ n := by
  rw [goldenRatio_pow, goldenConj_pow]
  ring

/-- [proved-standard; formal-checked] **The norm of `τⁿ` is `(−1)ⁿ`:** `L_n² − 5F_n² = 4(−1)ⁿ`. -/
theorem lucas_sq_sub_five_fib_sq (n : ℕ) :
    (lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1) ^ n := by
  have hprod : Real.goldenRatio ^ n * Real.goldenConj ^ n = (-1) ^ n := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj]
  rw [goldenRatio_pow, goldenConj_pow] at hprod
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : (((lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 : ℤ) : ℝ) = ((4 * (-1) ^ n : ℤ) : ℝ) := by
    push_cast
    linear_combination 4 * hprod + (Nat.fib n : ℝ) ^ 2 * h5
  exact Int.cast_injective h

/-- [proved-standard; formal-checked] The hidden colour `τ′` lies inside the unit interval. -/
theorem abs_goldenConj_lt_one : |Real.goldenConj| < 1 :=
  abs_lt.2 ⟨Real.neg_one_lt_goldenConj, by linarith [Real.goldenConj_neg]⟩

/-- [proved-standard; formal-checked] **The seen colour boosts:** `τⁿ < τⁿ⁺¹`. -/
theorem seen_grows (n : ℕ) : Real.goldenRatio ^ n < Real.goldenRatio ^ (n + 1) := by
  rw [pow_succ Real.goldenRatio n]
  exact lt_mul_of_one_lt_right (pow_pos Real.goldenRatio_pos n) Real.one_lt_goldenRatio

/-- [proved-standard; formal-checked] **The hidden colour contracts:** `|τ′ⁿ⁺¹| < |τ′ⁿ|`. -/
theorem hidden_shrinks (n : ℕ) : |Real.goldenConj ^ (n + 1)| < |Real.goldenConj ^ n| := by
  rw [pow_succ, abs_mul]
  exact mul_lt_of_lt_one_right (abs_pos.2 (pow_ne_zero n Real.goldenConj_ne_zero))
    abs_goldenConj_lt_one

/-- [proved-standard; formal-checked] `τ′ⁿ → 0`. -/
theorem hidden_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => Real.goldenConj ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_goldenConj_lt_one

/-- [definition] The inflation `a ↦ ab`, `b ↦ a`, with `a` written `true` and `b` written
`false`. -/
def inflate : List Bool → List Bool
  | [] => []
  | true :: w => true :: false :: inflate w
  | false :: w => true :: inflate w

/-- [definition] The length of a chain whose long gap `a` reads `x` and short gap `b` reads `1`. -/
def gaps {R : Type*} [CommRing R] (x : R) : List Bool → R
  | [] => 0
  | true :: w => x + gaps x w
  | false :: w => 1 + gaps x w

/-- [definition] The number of long gaps. -/
def countA : List Bool → ℕ
  | [] => 0
  | true :: w => countA w + 1
  | false :: w => countA w

/-- [definition] The number of short gaps. -/
def countB : List Bool → ℕ
  | [] => 0
  | true :: w => countB w
  | false :: w => countB w + 1

section Inflation

variable {R : Type*} [CommRing R]

/-- [proved-standard; formal-checked] **Inflation scales the chain by its root:** if
`x² = x + 1`, the inflated chain is `x` times as long. -/
theorem gaps_inflate {x : R} (hx : x ^ 2 = x + 1) (w : List Bool) :
    gaps x (inflate w) = x * gaps x w := by
  induction w with
  | nil => simp [inflate, gaps]
  | cons c w ih =>
    cases c with
    | true =>
      simp only [inflate, gaps, ih]
      linear_combination (-1 : R) * hx
    | false =>
      simp only [inflate, gaps, ih]
      ring

/-- [proved-standard; formal-checked] The `n`-th inflation of `a` has length `xⁿ⁺¹`. -/
theorem gaps_iterate {x : R} (hx : x ^ 2 = x + 1) (n : ℕ) :
    gaps x (inflate^[n] [true]) = x ^ (n + 1) := by
  induction n with
  | zero => simp [gaps]
  | succ n ih =>
    rw [Function.iterate_succ_apply', gaps_inflate hx, ih]
    ring

/-- [proved-standard; formal-checked] A chain's length is `#a · x + #b`. -/
theorem gaps_eq_count (x : R) (w : List Bool) :
    gaps x w = (countA w : R) * x + (countB w : R) := by
  induction w with
  | nil => simp [gaps, countA, countB]
  | cons c w ih =>
    cases c with
    | true =>
      simp only [gaps, countA, countB, ih]
      push_cast
      ring
    | false =>
      simp only [gaps, countA, countB, ih]
      push_cast
      ring

end Inflation

/-- [proved-standard; formal-checked] Inflation turns every tile into one long tile. -/
theorem countA_inflate (w : List Bool) : countA (inflate w) = countA w + countB w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    cases c with
    | true =>
      simp only [inflate, countA, countB, ih]
      omega
    | false =>
      simp only [inflate, countA, countB, ih]
      omega

/-- [proved-standard; formal-checked] Inflation turns every long tile into one short tile. -/
theorem countB_inflate (w : List Bool) : countB (inflate w) = countA w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    cases c with
    | true => simp only [inflate, countA, countB, ih]
    | false => simp only [inflate, countA, countB, ih]

/-- [proved-standard; formal-checked] **The tiles count by Fibonacci:** the `n`-th inflation of `a`
has `F_(n+1)` long and `F_n` short tiles. -/
theorem count_iterate (n : ℕ) :
    countA (inflate^[n] [true]) = Nat.fib (n + 1) ∧ countB (inflate^[n] [true]) = Nat.fib n := by
  induction n with
  | zero => simp [countA, countB]
  | succ n ih =>
    rw [Function.iterate_succ_apply', countA_inflate, countB_inflate, ih.1, ih.2]
    refine ⟨?_, rfl⟩
    rw [show n + 1 + 1 = n + 2 from rfl, Nat.fib_add_two]
    exact Nat.add_comm _ _

/-- [proved-standard; formal-checked] **`xⁿ⁺¹ = F_(n+1) x + F_n`** for a root of `x² = x + 1`, read
off the inflated chain. -/
theorem tile_count {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = x + 1) (n : ℕ) :
    x ^ (n + 1) = (Nat.fib (n + 1) : R) * x + (Nat.fib n : R) := by
  rw [← gaps_iterate hx n, gaps_eq_count, (count_iterate n).1, (count_iterate n).2]

/-- [proved-standard; formal-checked] **The seen colour of the inflated word is `τⁿ⁺¹`.** -/
theorem seen_length (n : ℕ) :
    gaps Real.goldenRatio (inflate^[n] [true]) = Real.goldenRatio ^ (n + 1) :=
  gaps_iterate Real.goldenRatio_sq n

/-- [proved-standard; formal-checked] **The hidden colour of the same word is `τ′ⁿ⁺¹`.** -/
theorem hidden_length (n : ℕ) :
    gaps Real.goldenConj (inflate^[n] [true]) = Real.goldenConj ^ (n + 1) :=
  gaps_iterate Real.goldenConj_sq n

/-- [proved-standard; formal-checked] **One word, two colours:** the hidden length of the inflated
word goes to `0` while its seen length grows. -/
theorem hidden_length_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => gaps Real.goldenConj (inflate^[n] [true])) Filter.atTop
      (nhds 0) := by
  have h := hidden_tendsto_zero.comp (Filter.tendsto_add_atTop_nat 1)
  refine h.congr fun n => ?_
  exact (hidden_length n).symm

end Holonics.Mathematics.FibonacciModelSet
