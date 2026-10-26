import HolonicsResearch.Mathematics.BaseAction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The rotor's step: a ring of `K` modes holds the number modulo every divisor of `bᴷ − 1`

The record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`
(§11) gives the rotor's law at the tower and owes (i) to #410: a ring of `K` modes stepped once a
digit holds `n` modulo every divisor of `10ᴷ − 1`, and a permutation keeps the passivity bound. The
digit move `x ↦ b x + d` and its action on characters are `Mathematics/BaseAction`.

[proved-standard; formal-checked] What is proved.

1. **The base closes its orbit on every divisor of `bᴷ − 1`** (`orbit_closes`,
   `pow_mod_orbit`): if `m ∣ bᴷ − 1` then `bᴷ = 1` in `ℤ/m`, so `bⁱ` depends on `i` only modulo `K`.
   This is the ring of `K` modes: the frequencies `c·bʲ` of one Galois orbit under the step.
2. **The positional rotor holds the number** (`ringReading`, `rotorStep`, `rotorStep_reading`,
   `rotor_holds_number`). Keep `K` integer modes; a digit rotates them one place and adds itself
   at mode `0`. When `bᴷ = 1` in `ℤ/m`, the reading `∑_j v_j bʲ` of the stepped modes is the digit
   move `b·x + d` of the old reading, so stepping a word from rest holds the word's number modulo
   `m`, for every `m ∣ bᴷ − 1` at once (four modes of base 10 hold `9999 = 3²·11·101`).
3. **The keyed rotor is the generator and the modulator in one move** (`keyedStep`,
   `keyed_rotor_step`, `keyed_rotor_wraps`, `keyed_rotor_reads`, `keyed_rotor_from_rest`). Let mode
   `j` carry the character of frequency `c·bʲ`. A digit `d` hands mode `j` the old mode `j + 1`
   (the generator, the shift of frequency) turned by `ψ(c·bʲ·d)` (the modulator, the turn by the
   arriving digit): `ψ(c·bʲ·(b n + d)) = ψ(c·bʲ·d)·ψ(c·bʲ⁺¹·n)`. Mode `j + K` is mode `j` when
   `bᴷ = 1`. Read from rest, mode `j` after the word is exactly `ψ(c·bʲ·n)`: this is the equation
   at the consumer that the rotor loop's next build fixes.
4. **A monomial step keeps the power** (`monomial_step_keeps_power`). A step that hands each mode
   exactly one mode's state, multiplied by a unit-modulus turn, keeps `∑_j |v_j|²`. The keyed rotor
   is such a step, so the tower's passivity bound holds unchanged.

Consumers: the atlas rows `hnn.tower-rotor`, `radix.rotor-planes` and `radix.rotor-galois-orbit`.
-/

namespace Holonics.Mathematics.RotorStep

open Holonics.Mathematics.BaseAction

/-- [proved-standard; formal-checked] **The base closes its orbit on every divisor of `bᴷ − 1`.** -/
theorem orbit_closes {b m K : ℕ} (hb : 0 < b) (h : m ∣ b ^ K - 1) : (b : ZMod m) ^ K = 1 := by
  have h1 : 1 ≤ b ^ K := pow_pos hb K
  have h0 : ((b ^ K - 1 : ℕ) : ZMod m) = 0 := (CharP.cast_eq_zero_iff (ZMod m) m _).mpr h
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
  exact h0

/-- [proved-standard; formal-checked] On such a ring `bⁱ` depends on `i` only modulo `K`. -/
theorem pow_mod_orbit {R : Type*} [Monoid R] {x : R} {K : ℕ} (h : x ^ K = 1) (i : ℕ) :
    x ^ (i % K) = x ^ i := by
  conv_rhs => rw [← Nat.mod_add_div i K, pow_add, pow_mul, h, one_pow, mul_one]

section Positional

variable {K : ℕ} [NeZero K]

/-- [definition] The reading of `K` integer modes in base `b` on the ring `ℤ/m`:
`∑_j v_j bʲ`. -/
def ringReading (m b : ℕ) (v : ZMod K → ℤ) : ZMod m :=
  ∑ j : ZMod K, (v j : ZMod m) * (b : ZMod m) ^ j.val

/-- [definition] The rotor's step: rotate the modes one place and add the digit at mode `0`. -/
def rotorStep (v : ZMod K → ℤ) (d : ℤ) : ZMod K → ℤ :=
  fun j => v (j - 1) + if j = 0 then d else 0

/-- [proved-standard; formal-checked] **The rotor's step is the digit move on the reading**, on
every ring `ℤ/m` with `bᴷ = 1`. -/
theorem rotorStep_reading {m b : ℕ} (h : (b : ZMod m) ^ K = 1) (v : ZMod K → ℤ) (d : ℤ) :
    ringReading m b (rotorStep v d) = (b : ZMod m) * ringReading m b v + (d : ZMod m) := by
  have hnat : ∀ a : ℕ, (b : ZMod m) ^ ((a : ZMod K).val) = (b : ZMod m) ^ a := by
    intro a
    rw [ZMod.val_natCast, pow_mod_orbit h]
  have hexp : ∀ j : ZMod K, (b : ZMod m) ^ (j + 1).val = (b : ZMod m) * (b : ZMod m) ^ j.val := by
    intro j
    have hj : j + 1 = ((j.val + 1 : ℕ) : ZMod K) := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [hj, hnat, pow_succ, mul_comm]
  have hshift : ∑ j : ZMod K, ((v (j - 1) : ℤ) : ZMod m) * (b : ZMod m) ^ j.val =
      ∑ j : ZMod K, (v j : ZMod m) * (b : ZMod m) ^ (j + 1).val :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ fun j => by simp
  have hdigit : ∑ j : ZMod K, (((if j = 0 then d else 0 : ℤ)) : ZMod m) * (b : ZMod m) ^ j.val =
      (d : ZMod m) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h0
      exact absurd (Finset.mem_univ 0) h0
  simp only [ringReading, rotorStep, Int.cast_add, add_mul, Finset.sum_add_distrib, hshift, hdigit,
    hexp, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- [proved-standard; formal-checked] **Stepping a word holds its number:** started from modes
reading `x`, the rotor stepped through the digits reads the word folded into `x`, modulo every
`m` with `bᴷ = 1` in `ℤ/m`. -/
theorem rotor_holds_number {m b : ℕ} (h : (b : ZMod m) ^ K = 1) (ds : List ℤ)
    (v : ZMod K → ℤ) (x : ℤ) (hv : ringReading m b v = (x : ZMod m)) :
    ringReading m b (ds.foldl rotorStep v) =
      ((ds.foldl (fun y d => digitMove (b : ℤ) d y) x : ℤ) : ZMod m) := by
  induction ds generalizing v x with
  | nil => simpa using hv
  | cons d ds ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [rotorStep_reading h, hv]
    simp only [digitMove, Int.cast_add, Int.cast_mul, Int.cast_natCast]

end Positional

section Keyed

variable {R M : Type*} [CommRing R] [CommMonoid M]

/-- [definition] The keyed rotor's step on modes indexed by `j`: mode `j` takes the old mode
`j + 1`, turned by the digit's phase at frequency `c·bʲ`. -/
def keyedStep (ψ : AddChar R M) (c b d : R) (h : ℕ → M) : ℕ → M :=
  fun j => ψ (c * b ^ j * d) * h (j + 1)

/-- [proved-standard; formal-checked] **The generator and the modulator are one move:**
`ψ(c·bʲ·(b n + d)) = ψ(c·bʲ·d)·ψ(c·bʲ⁺¹·n)`. -/
theorem keyed_rotor_step (ψ : AddChar R M) (c b d n : R) (j : ℕ) :
    ψ (c * b ^ j * digitMove b d n) = ψ (c * b ^ j * d) * ψ (c * b ^ (j + 1) * n) := by
  rw [digitMove_on_characters, show b * (c * b ^ j) = c * b ^ (j + 1) by ring]

/-- [proved-standard; formal-checked] **The ring of `K` modes closes:** when `bᴷ = 1`, mode
`j + K` is mode `j`. -/
theorem keyed_rotor_wraps (ψ : AddChar R M) {b : R} {K : ℕ} (h : b ^ K = 1) (c n : R) (j : ℕ) :
    ψ (c * b ^ (j + K) * n) = ψ (c * b ^ j * n) := by
  rw [pow_add, h, mul_one]

/-- [proved-standard; formal-checked] **The keyed rotor reads the word:** started from the modes of
`n`, after the digits mode `j` is the character of frequency `c·bʲ` at the word folded into `n`. -/
theorem keyed_rotor_reads (ψ : AddChar R M) (c b : R) (ds : List R) (n : R) :
    ds.foldl (fun h d => keyedStep ψ c b d h) (fun j => ψ (c * b ^ j * n)) =
      fun j => ψ (c * b ^ j * ds.foldl (fun y d => digitMove b d y) n) := by
  induction ds generalizing n with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons]
    rw [← ih (digitMove b d n)]
    congr 1
    funext j
    simp only [keyedStep]
    rw [keyed_rotor_step]

/-- [proved-standard; formal-checked] **From rest, mode `j` is exactly `ψ(c·bʲ·n)`** for the
word's number `n`. -/
theorem keyed_rotor_from_rest (ψ : AddChar R M) (c b : R) (ds : List R) :
    ds.foldl (fun h d => keyedStep ψ c b d h) (fun _ => 1) =
      fun j => ψ (c * b ^ j * ds.foldl (fun y d => digitMove b d y) 0) := by
  have h0 : (fun _ : ℕ => (1 : M)) = fun j => ψ (c * b ^ j * 0) := by
    funext j
    rw [mul_zero, AddChar.map_zero_eq_one]
  rw [h0, keyed_rotor_reads]

end Keyed

/-- [proved-standard; formal-checked] **A monomial step keeps the power:** handing each mode one
mode's state, turned by a unit-modulus factor, keeps `∑_j |v_j|²`. -/
theorem monomial_step_keeps_power {ι : Type*} [Fintype ι] (σ : ι ≃ ι) (u v : ι → ℂ)
    (hu : ∀ j, Complex.normSq (u j) = 1) :
    ∑ j, Complex.normSq (u j * v (σ j)) = ∑ j, Complex.normSq (v j) := by
  simp only [map_mul, hu, one_mul]
  exact Equiv.sum_comp σ (fun j => Complex.normSq (v j))

end Holonics.Mathematics.RotorStep
