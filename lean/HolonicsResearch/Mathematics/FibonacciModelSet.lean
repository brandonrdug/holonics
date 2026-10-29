import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-!
# The Fibonacci chain: inflation boosts the seen colour and contracts the hidden one

The record `research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md`
(atlas `quasi.fibonacci-model-set`) reads the Fibonacci quasicrystal as a model set: physical space
is one Galois colour of `ℤ[τ]`, the window lives in the conjugate, and inflation by the Pisot unit
`τ` boosts the seen colour and contracts the hidden one, so the hidden colour is held as a window,
never as a store. #410 owes it; this file proves the arithmetic of the two colours, the
inflation `a ↦ ab`, `b ↦ a`, and the window statement, exactly (`τ = Real.goldenRatio`,
`τ′ = Real.goldenConj`).

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

7. **The chain is the model set** (`window`, `legal`, `legal_inflate`, `legal_iterate`,
   `legal_prefix`, `vertex_mem_window`, `small_step`, `legal_cover`, `mem_window_vertex`,
   `vertices_eq_model_set`): every vertex `m + nτ` of the chain (`m` short and `n` long tiles from
   the origin) has its conjugate `m + nτ′` in the window `[−1, τ − 1)`, and every such point of
   `ℤ[τ] ∩ [0, ∞)` is a vertex. The chain is one infinite word: each inflation of `a` is a prefix
   of the next (`inflate_append`, `iterate_prefix`).

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

/-! ## The window

The chain is read in the hidden colour as a walk: starting at `0`, a long tile `a` moves the hidden
coordinate by `τ′` and a short tile `b` by `1`, and the walk is legal when it takes `a` exactly on
`(τ − 2, τ − 1)` and `b` exactly on `(−1, τ − 2)`. Inflation multiplies a legal walk by `τ′`
(`legal_inflate`), so every inflation of `a` is legal and its vertices lie over the window; a
point of `ℤ[τ]` over the window between two consecutive vertices would differ from the first by an
element whose two colours are both shorter than `τ`, and the only such elements are `0` and `1`
(`small_step`), which the walk's rule excludes. -/

section Window

local notation "τ" => Real.goldenRatio
local notation "ψ" => Real.goldenConj


/-- [definition] The window `[−1, τ − 1)` in the hidden colour. -/
def window : Set ℝ := Set.Ico (-1) (Real.goldenRatio - 1)

/-- [definition] A walk read in the hidden colour from `x`: a long tile is taken exactly where
`τ − 2 < x < τ − 1`, a short one exactly where `−1 < x < τ − 2`, each step moving `x` by the tile's
hidden length (`τ′` or `1`), and the walk ends inside `(−1, τ − 1)`. -/
def legal : ℝ → List Bool → Prop
  | x, [] => -1 < x ∧ x < Real.goldenRatio - 1
  | x, true :: w => Real.goldenRatio - 2 < x ∧ x < Real.goldenRatio - 1 ∧
      legal (x + Real.goldenConj) w
  | x, false :: w => -1 < x ∧ x < Real.goldenRatio - 2 ∧ legal (x + 1) w

/-- [proved-standard; formal-checked] **Inflation is multiplication by `τ′` in the hidden colour:**
a legal walk from `x` inflates to a legal walk from `τ′x`. -/
theorem legal_inflate (w : List Bool) (x : ℝ) (h : legal x w) : legal (ψ * x) (inflate w) := by
  have hs := Real.goldenRatio_sq
  have h1 := Real.one_lt_goldenRatio
  have h2 := Real.goldenRatio_lt_two
  have hψ : ψ = 1 - τ := by linarith [Real.goldenRatio_add_goldenConj]
  induction w generalizing x with
  | nil =>
    obtain ⟨ha, hb⟩ := h
    simp only [inflate, legal, hψ]
    constructor <;> nlinarith [mul_pos (by linarith : (0 : ℝ) < τ - 1) (by linarith : 0 < x + 1),
      mul_pos (by linarith : (0 : ℝ) < τ - 1) (by linarith : 0 < τ - 1 - x)]
  | cons c w ih =>
    cases c with
    | true =>
      obtain ⟨ha, hb, hw⟩ := h
      have hi := ih (x + ψ) hw
      simp only [inflate, legal]
      rw [show ψ * x + ψ + 1 = ψ * (x + ψ) by rw [hψ]; nlinarith]
      refine ⟨?_, ?_, ?_, ?_, hi⟩ <;> rw [hψ] <;>
        nlinarith [mul_pos (by linarith : (0 : ℝ) < τ - 1) (by linarith : 0 < x - (τ - 2)),
          mul_pos (by linarith : (0 : ℝ) < τ - 1) (by linarith : 0 < τ - 1 - x)]
    | false =>
      obtain ⟨ha, hb, hw⟩ := h
      have hi := ih (x + 1) hw
      simp only [inflate, legal]
      rw [show ψ * x + ψ = ψ * (x + 1) by ring]
      refine ⟨?_, ?_, hi⟩ <;> rw [hψ] <;>
        nlinarith [mul_pos (by linarith : (0 : ℝ) < τ - 1) (by linarith : 0 < x + 1),
          mul_pos (by linarith : (0 : ℝ) < τ - 1) (by linarith : 0 < τ - 2 - x)]

/-- [proved-standard; formal-checked] Every inflation of `a` is a legal walk from `0`. -/
theorem legal_iterate (n : ℕ) : legal 0 (inflate^[n] [true]) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id, legal, zero_add]
    have h1 := Real.one_lt_goldenRatio
    have h2 := Real.goldenRatio_lt_two
    have := Real.goldenRatio_add_goldenConj
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simpa using legal_inflate _ 0 ih

/-- [proved-standard; formal-checked] Along a legal walk every prefix lands in `(−1, τ − 1)`. -/
theorem legal_prefix (w : List Bool) (x : ℝ) (h : legal x w) (p : List Bool) (hp : p <+: w) :
    -1 < x + gaps ψ p ∧ x + gaps ψ p < τ - 1 := by
  have h1 := Real.one_lt_goldenRatio
  induction w generalizing x p with
  | nil =>
    rw [List.prefix_nil.mp hp]
    simpa [gaps, legal] using h
  | cons c w ih =>
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
    · cases c with
      | true => obtain ⟨ha, hb, _⟩ := h; simp only [gaps, add_zero]; constructor <;> linarith
      | false => obtain ⟨ha, hb, _⟩ := h; simp only [gaps, add_zero]; constructor <;> linarith
    · cases c with
      | true =>
        have := ih (x + ψ) h.2.2 t ht
        simp only [gaps]; constructor <;> linarith [this.1, this.2]
      | false =>
        have := ih (x + 1) h.2.2 t ht
        simp only [gaps]; constructor <;> linarith [this.1, this.2]

/-- [proved-standard; formal-checked] **Every vertex lies over the window:** each vertex
`m + nτ` of the chain (`m` short and `n` long tiles from the origin) has its conjugate `m + nτ′` in
`[−1, τ − 1)`. -/
theorem vertex_mem_window (N : ℕ) (p : List Bool) (hp : p <+: inflate^[N] [true]) :
    (countB p : ℝ) + countA p * ψ ∈ window := by
  have h := legal_prefix _ 0 (legal_iterate N) p hp
  rw [gaps_eq_count, zero_add] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- [proved-standard; formal-checked] **The two colours of a short step:** an element `a + bτ` of
`ℤ[τ]` with `0 ≤ a + bτ < τ` and `|a + bτ′| < τ` is `0` or `1`. -/
theorem small_step (a b : ℤ) (h0 : 0 ≤ (a : ℝ) + b * τ) (h1 : (a : ℝ) + b * τ < τ)
    (h2 : -τ < (a : ℝ) + b * ψ) (h3 : (a : ℝ) + b * ψ < τ) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) := by
  have hg1 := Real.one_lt_goldenRatio
  have hg2 := Real.goldenRatio_lt_two
  have hψ : ψ = 1 - τ := by linarith [Real.goldenRatio_add_goldenConj]
  rw [hψ] at h2 h3
  have hb2 : b < 2 := by
    by_contra hc
    have hc' : (2 : ℝ) ≤ b := by exact_mod_cast not_lt.mp hc
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ b - 2) (by linarith : (0 : ℝ) ≤ 2 * τ - 1)]
  have hb0 : 0 ≤ b := by
    by_contra hc
    have hc' : (b : ℝ) ≤ -1 := by exact_mod_cast (show b ≤ -1 by omega)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -1 - b) (by linarith : (0 : ℝ) ≤ 2 * τ - 1)]
  interval_cases b
  · have ha0 : (0 : ℝ) ≤ a := by simpa using h0
    have ha2 : (a : ℝ) < 2 := by simp at h1; linarith
    have : 0 ≤ a := by exact_mod_cast ha0
    have : a < 2 := by exact_mod_cast ha2
    interval_cases a <;> simp
  · exfalso
    have ha1 : (a : ℝ) < 0 := by push_cast at h1; linarith
    have ha2 : (-2 : ℝ) < a := by push_cast at h0; linarith
    have : a < 0 := by exact_mod_cast ha1
    have : -2 < a := by exact_mod_cast ha2
    have ha : a = -1 := by omega
    subst ha
    push_cast at h2
    linarith

/-- [proved-standard; formal-checked] **A legal walk covers its window:** every point of `ℤ[τ]`
between the walk's start and end whose hidden colour lies in the window is a vertex of the walk. -/
theorem legal_cover (w : List Bool) (x : ℝ) (h : legal x w) (a b : ℤ)
    (h0 : 0 ≤ (a : ℝ) + b * τ) (hlt : (a : ℝ) + b * τ < gaps τ w)
    (hw1 : -1 ≤ x + (a + b * ψ)) (hw2 : x + (a + b * ψ) < τ - 1) :
    ∃ p, p <+: w ∧ (countB p : ℤ) = a ∧ (countA p : ℤ) = b := by
  have hg1 := Real.one_lt_goldenRatio
  induction w generalizing x a b with
  | nil => simp [gaps] at hlt; linarith
  | cons c w ih =>
    have hx : -1 < x ∧ x < τ - 1 := by
      cases c with
      | true => obtain ⟨ha, hb, _⟩ := h; constructor <;> linarith
      | false => obtain ⟨ha, hb, _⟩ := h; constructor <;> linarith
    cases c with
    | true =>
      by_cases hs : (a : ℝ) + b * τ < τ
      · rcases small_step a b h0 hs (by linarith) (by linarith) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨[], List.nil_prefix, rfl, rfl⟩
        · exfalso; obtain ⟨ha, _, _⟩ := h; push_cast at hw2; linarith
      · obtain ⟨p, hp, hpa, hpb⟩ := ih (x + ψ) h.2.2 a (b - 1) (by push_cast; linarith)
          (by simp only [gaps] at hlt; push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith)
        refine ⟨true :: p, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, ?_, ?_⟩
        · simpa [countB] using hpa
        · simp only [countA]; push_cast; omega
    | false =>
      by_cases hs : (a : ℝ) + b * τ < 1
      · rcases small_step a b h0 (by linarith) (by linarith) (by linarith) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨[], List.nil_prefix, rfl, rfl⟩
        · exfalso; push_cast at hs; linarith
      · obtain ⟨p, hp, hpa, hpb⟩ := ih (x + 1) h.2.2 (a - 1) b (by push_cast; linarith)
          (by simp only [gaps] at hlt; push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith)
        refine ⟨false :: p, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, ?_, ?_⟩
        · simp only [countB]; push_cast; omega
        · simpa [countA] using hpb

/-- [proved-standard; formal-checked] **Every point over the window is a vertex:** each
`m + nτ ≥ 0` in `ℤ[τ]` whose conjugate `m + nτ′` lies in `[−1, τ − 1)` is a vertex of the chain. -/
theorem mem_window_vertex (m n : ℤ) (h0 : 0 ≤ (m : ℝ) + n * τ)
    (hw : (m : ℝ) + n * ψ ∈ window) :
    ∃ N p, p <+: inflate^[N] [true] ∧ (countB p : ℤ) = m ∧ (countA p : ℤ) = n := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((m : ℝ) + n * τ) Real.one_lt_goldenRatio
  refine ⟨k, legal_cover _ 0 (legal_iterate k) m n h0 ?_ (by simpa using hw.1)
    (by simpa using hw.2)⟩
  rw [seen_length]
  exact hk.trans (seen_grows k)

/-- [proved-standard; formal-checked] **The Fibonacci chain is the model set:** its vertices are
exactly the points `m + nτ ≥ 0` of `ℤ[τ]` whose conjugate `m + nτ′` lies in the window
`[−1, τ − 1)`. -/
theorem vertices_eq_model_set :
    {u : ℝ | ∃ N p, p <+: inflate^[N] [true] ∧ u = gaps τ p} =
      {u : ℝ | ∃ m n : ℤ, u = m + n * τ ∧ 0 ≤ u ∧ (m : ℝ) + n * ψ ∈ window} := by
  ext u
  constructor
  · rintro ⟨N, p, hp, rfl⟩
    refine ⟨countB p, countA p, ?_, ?_, ?_⟩
    · rw [gaps_eq_count]; push_cast; ring
    · rw [gaps_eq_count]; have := Real.goldenRatio_pos; positivity
    · push_cast; exact vertex_mem_window N p hp
  · rintro ⟨m, n, rfl, h0, hw⟩
    obtain ⟨N, p, hp, hm, hn⟩ := mem_window_vertex m n h0 hw
    refine ⟨N, p, hp, ?_⟩
    rw [gaps_eq_count, ← hm, ← hn]
    push_cast; ring

/-- [proved-standard; formal-checked] Inflation carries a concatenation to a concatenation. -/
theorem inflate_append (u v : List Bool) : inflate (u ++ v) = inflate u ++ inflate v := by
  induction u with
  | nil => rfl
  | cons c u ih => cases c <;> simp [inflate, ih]

/-- [proved-standard; formal-checked] **The chain is one word:** each inflation of `a` is a prefix of
the next, so the vertices of all of them are the vertices of one infinite chain. -/
theorem iterate_prefix (n : ℕ) : inflate^[n] [true] <+: inflate^[n + 1] [true] := by
  induction n with
  | zero => exact ⟨[false], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨inflate t, ?_⟩
    rw [Function.iterate_succ_apply' _ (n + 1)]
    conv_rhs => rw [← ht]
    rw [inflate_append, ← Function.iterate_succ_apply' inflate n]

end Window

end Holonics.Mathematics.FibonacciModelSet
