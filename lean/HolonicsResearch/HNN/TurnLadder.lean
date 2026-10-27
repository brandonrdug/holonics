import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# The turn ladder: a fixed mode turns many times over its memory, a scaled mode less than once

The record `research/records/2026-10-25_ONE_LISTENER_HEARS_GSM8K_MNIST_AND_SPEECH_AS_SECTIONS_OF_ONE_PASSAGE.md`
(section "Why the state forgets the image", atlas `hnn.tower-turn-ladder`) founds each level's
modes on a ladder (`hnn::tower::{TurnLadder, Tower::found_on}`). Place `p` of a ladder of `J`
turns sits on rung `s = ⌊p/J⌋ + 1` with turn index `j = p mod J` and radius
`ρ = 1 − 2^(−min(s, M))`, `M` the margin's rung (`12` in the tower). A fixed mode turns by `πj/J` a
step; a scaled one by `πj/(J·2^(m−1))`, `m = min(s, M)`. #410 owes the turns over a mode's
memory; this file proves them.

[proved-derived; formal-checked] What is proved.

1. **The rung's memory is `2^min(s, M)`** (`memory`): `1/(1 − ρ) = 2^min(s, M)`. A place is its
   rung and turn index (`place_eq`, `turnIndex_lt`).
2. **A fixed mode turns `2^(s−1) j/J` times over its memory** (`fixed_turn_over_memory`,
   `fixed_whole_turns`): `2^s` steps of `πj/J` turn `2π · 2^(s−1) j/J`, and where `J` divides
   `2^(s−1) j` the mode `u = e^(iπj/J)` is back where it began, `u^(2^s) = 1`, after that whole
   number of turns. The slow rungs turn many times, so a class's phase is set by its place in the
   passage.
3. **A scaled mode turns `2πj/J` over its memory on every rung** (`scaled_turn_over_memory`), the
   same up to the margin and past it (where `m` stays `M`), and **never once around within what it
   remembers** (`scaled_no_full_turn`): for `0 < j < J` and `0 < n ≤ 2^m`, `u^n ≠ 1`, since
   `u = ζ^j` for the primitive `J·2^m`-th root `ζ = e^(2πi/(J·2^m))` and `0 < jn < J·2^m`.
4. **A bank of both takes half each over the same rungs** (`both_halves`): mode `k < 2N` of a
   bank of `2N` modes sits at place `k mod N`, the fixed half `k < N` at `k` and the scaled half at
   `k − N`, so the halves hold the same places, hence the same rungs and turn indices, and differ
   only in their moves.

The computational object is the helical pair interaction's ring: a mode is a parametron ring whose
turn per step is its winding and whose radius is its memory. Of the winding guide's six general
objects this touches the helix (the turn per step and its whole turns) and faces and placement
(the rung and turn index of a place); the pair, the cell holonomy, the tube and the tower thread
stay attached.

Consumers: the atlas row `hnn.tower-turn-ladder` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.TurnLadder

open Complex

/-! ## 1. The rung and its memory -/

/-- The rung of place `p` on a ladder of `J` turns, `s = ⌊p/J⌋ + 1`. -/
def rung (J p : ℕ) : ℕ := p / J + 1

/-- The turn index of place `p`, `j = p mod J`. -/
def turnIndex (J p : ℕ) : ℕ := p % J

/-- The radius of rung `s` under the margin's rung `M`, `ρ = 1 − 2^(−min(s, M))`. -/
def radius (M s : ℕ) : ℚ := 1 - 1 / 2 ^ min s M

/-- [proved-derived; formal-checked] **The rung's memory**: `1/(1 − ρ) = 2^min(s, M)`. -/
theorem memory (M s : ℕ) : 1 / (1 - radius M s) = 2 ^ min s M := by
  rw [radius, sub_sub_cancel, one_div_one_div]

/-- [proved-derived; formal-checked] A place is its rung and turn index, `p = (s − 1)J + j`. -/
theorem place_eq (J p : ℕ) : p = (rung J p - 1) * J + turnIndex J p := by
  simp only [rung, turnIndex, Nat.add_sub_cancel]
  exact (Nat.div_add_mod' p J).symm

/-- [proved-derived; formal-checked] The turn index lies below `J`. -/
theorem turnIndex_lt {J : ℕ} (hJ : 0 < J) (p : ℕ) : turnIndex J p < J :=
  Nat.mod_lt p hJ

/-! ## 2. The fixed ladder -/

/-- [proved-derived; formal-checked] **The fixed mode's turn over its memory**: `2^s` steps of
`πj/J` turn `2π · 2^(s−1) j/J`. -/
theorem fixed_turn_over_memory (J j s : ℕ) (hs : 1 ≤ s) :
    (2 : ℝ) ^ s * (Real.pi * j / J) = 2 * Real.pi * (2 ^ (s - 1) * j / J) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-- [proved-derived; formal-checked] **Whole turns**: where `J` divides `2^(s−1) j`, the fixed mode
`u = e^(iπj/J)` is back where it began after its memory, `u^(2^s) = 1`, having turned
`2^(s−1) j/J` times. -/
theorem fixed_whole_turns {J j s : ℕ} (hJ : J ≠ 0) (hs : 1 ≤ s) (hdvd : J ∣ 2 ^ (s - 1) * j) :
    Complex.exp (Real.pi * j / J * I) ^ (2 ^ s) = 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hJ' : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have hq' : (2 : ℂ) ^ t * j = J * q := by exact_mod_cast hq
  have h1 : (2 : ℂ) ^ t * j / J = q := by
    rw [div_eq_iff hJ']
    linear_combination hq'
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨q, ?_⟩
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * I) * h1

/-! ## 3. The scaled ladder -/

/-- [proved-derived; formal-checked] **The scaled mode's turn over its memory is the same on every
rung**: with `m = min(s, M) ≥ 1`, `2^m` steps of `πj/(J·2^(m−1))` turn `2πj/J`. -/
theorem scaled_turn_over_memory {J : ℕ} (hJ : J ≠ 0) (j m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ m * (Real.pi * j / (J * 2 ^ (m - 1))) = 2 * Real.pi * j / J := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
  have h2 : (2 : ℝ) ^ t ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [mul_div_assoc', div_eq_div_iff (mul_ne_zero hJ' h2) hJ']
  ring

/-- [proved-derived; formal-checked] The scaled mode is a power of a primitive root:
`e^(iπj/(J·2^(m−1))) = ζ^j` with `ζ = e^(2πi/(J·2^m))`. -/
theorem scaled_eq_pow {J : ℕ} (hJ : J ≠ 0) (j m : ℕ) (hm : 1 ≤ m) :
    Complex.exp (Real.pi * j / (J * 2 ^ (m - 1)) * I) =
      Complex.exp (2 * Real.pi * I / ((J * 2 ^ m : ℕ) : ℂ)) ^ j := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← Complex.exp_nat_mul]
  congr 1
  have hJ' : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have h2 : (2 : ℂ) ^ t ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  rw [pow_succ]
  field_simp

/-- [proved-derived; formal-checked] **A scaled mode never turns once around within what it
remembers**: for `0 < j < J` and `0 < n ≤ 2^m`, `e^(iπj/(J·2^(m−1)))^n ≠ 1`. -/
theorem scaled_no_full_turn {J j m n : ℕ} (hm : 1 ≤ m) (hj : 0 < j) (hjJ : j < J) (hn : 0 < n)
    (hnm : n ≤ 2 ^ m) :
    Complex.exp (Real.pi * j / (J * 2 ^ (m - 1)) * I) ^ n ≠ 1 := by
  have hJ : J ≠ 0 := by omega
  have hN : J * 2 ^ m ≠ 0 := mul_ne_zero hJ (pow_ne_zero _ two_ne_zero)
  have hζ := Complex.isPrimitiveRoot_exp (J * 2 ^ m) hN
  rw [scaled_eq_pow hJ j m hm, ← pow_mul, ne_eq, hζ.pow_eq_one_iff_dvd]
  intro hdvd
  have hpos : 0 < j * n := Nat.mul_pos hj hn
  have hle := Nat.le_of_dvd hpos hdvd
  have hlt : j * n < J * 2 ^ m :=
    calc j * n ≤ j * 2 ^ m := Nat.mul_le_mul_left j hnm
      _ < J * 2 ^ m := Nat.mul_lt_mul_of_pos_right hjJ (by positivity)
  exact absurd hle (not_le.mpr hlt)

/-! ## 4. Both ladders in one bank -/

/-- [proved-derived; formal-checked] **A bank of both takes half each over the same places**: mode
`k < 2N` sits at place `k mod N`, which is `k` on the fixed half and `k − N` on the scaled half. -/
theorem both_halves {N k : ℕ} (hk : k < 2 * N) :
    (k < N → k % N = k) ∧ (N ≤ k → k % N = k - N) := by
  constructor
  · exact Nat.mod_eq_of_lt
  · intro h
    rw [Nat.mod_eq_sub_mod h]
    exact Nat.mod_eq_of_lt (by omega)

end Holonics.HNN.TurnLadder
