import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Holonics.Geometry.PhaseCarry
import Holonics.Aeon.Clock.Epoch
import Holonics.HNN.RegionCounts

/-!
# The arithmetic contract: a numeral is a face of a counting navigator, its producer is a key

[definition] `research/records/2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md`
(THE_REBUILD U6, the text chart audit's §4 item 3). A numeral met in a stream is the radix
receiver's face of an integer: its digit word in base `b` is the reading of an odometer of radix
`b` (`Geometry/PhaseCarry`), each digit a phase and each carry a winding passed up. Its producer is
a navigator with its initial configuration: the pair's carry-free combination (a pointwise sum for
`+`, a convolution for `·`, a repeated convolution for `^`) followed by one carry cascade. This
module states what the record derives and proves.

[proved-derived; formal-checked] What is proved.

1. **One carry cascade, many producers; the consumer equation.** `carryWord b c w` reads each
   place's total on the circle of `b` steps, emits its phase and passes its winding up
   (`carryWord_cons`); it keeps the value, `value (carryWord b c w) = value w + c`
   (`carryWord_value`), and emits digits below `b` (`carryWord_lt`). The pointwise sum and the
   convolution keep the value additively and multiplicatively (`ofDigits_zipAdd`,
   `ofDigits_conv`), so `decode_b (T_native (encode_b a, encode_b c)) = T (a, c)` for `T = +` and
   `T = ·` in every base `b ≥ 2` (`consumer_add`, `consumer_mul`), and for `^` by repeated
   convolution (`consumer_pow`): the consequence square closes, and it closes alike in any two
   bases (`consumer_rebase`).
2. **The carry is the section flux.** The carry a place passes up is the signed crossing count of
   that place's wheel's section `{x | b ∣ x}` over any aeon of its lift from `0` to the place's
   total (`carry_is_section_flux`, over `Aeon/Clock/Epoch.signed_count_is_flux`, as U5's
   `HNN/Moment.SelectiveDecl.carryIn_is_section_flux` states it for a ring).
3. **The multiplication table is the map of digit-pair carries.** A pair `(x, y)` of digits maps
   to the division with remainder `x y = b ⌊x y / b⌋ + (x y mod b)` (`table_div_rem`); along a row
   the carry advances by the phase carry of the rate-`x` clock (`tableCarry_succ`, through
   `PhaseCarry.winding_add`), and the row's digits repeat with period `b / gcd(x, b)`
   (`tableDigit_periodic`).
4. **Provenance: one face, three producers, separated by their jets.** `2 + 2 = 2 · 2 = 2 ^ 2 = 4`
   (`one_face_three_producers`). Along the right operand's clock the jets are
   `(a + k, 1, 0)`, `(a k, a, 0)` and `(a^k, a^k (a − 1), a^k (a − 1)²)` (`jet_add`, `jet_mul`,
   `jet_pow`); for `a ≥ 2` the jet to second order separates every two producers
   (`jet_separates`), whatever keys `a, a' ≥ 2` the two hold (`jet_separates_across_keys`); the
   face with the first difference ties only `·` and `^`, only at `(a, k) = (2, 1)`
   (`mul_pow_first_jet_tie_iff`). At `a = 0`, `·` and `^` are one species along
   that clock (`zero_mul_pow_species`) and the left operand's clock separates them
   (`left_clock_separates`). The sum and the product satisfy the recurrence with the double root
   `1` and no first-order one (`add_free_fall`, `mul_free_fall`, `add_no_single_mode`,
   `mul_no_single_mode`): free fall; the power satisfies `f(k + 1) = a f(k)` (`pow_boost`): a
   dilation.
5. **Powers of two lock in bases `2^j` and never in base 10.** `len_(2^j)(2^k) = ⌊k/j⌋ + 1`
   (`digits_length_two_pow`); `2^T ≠ 10^S` for `T ≥ 1` (`two_pow_ne_ten_pow`), and the base-10
   digit counts of `2^k` are never eventually periodic (`ten_digit_count_never_locks`).
6. **The holds sheet.** The Krichevsky–Trofimov face of `N` holding results multiplies to
   `C(2N, N)/4^N` (`holds_sheet_telescope`): their code is `2N − log₂ C(2N, N)` bits.

The computational object is the helical pair interaction: two digit vectors meet at a pair port
(the convolution pairs digit `i` with digit `l` at place `i + l`), and the odometer carries the
result. Of the winding guide's six general objects this module touches the helix (the carry
cascade), the pair (the convolution and the table), faces and placement (the numeral as a radix
face, the jets) and the tower thread (bases `2^j` restrict base 2); the cell holonomy and the tube
stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.ArithmeticContract

open Holonics.Geometry
open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Winding Holonics.Aeon.Clock.Epoch

/-! ## 1. One carry cascade and the consumer equation -/

/-- [definition] **The pointwise sum** of two digit words, least significant first, before carry. -/
def zipAdd : List ℕ → List ℕ → List ℕ
  | [], v => v
  | u :: us, [] => u :: us
  | u :: us, v :: vs => (u + v) :: zipAdd us vs

/-- [definition] **The convolution** of two digit words before carry: `x · ys + b · (xs * ys)`. -/
def conv : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: xs, ys => zipAdd (ys.map (x * ·)) (0 :: conv xs ys)

/-- [definition] **The carry cascade**: each place's total `w + c` is read on the circle of `b`
steps; its phase is emitted and its winding passed up; the last carry is emitted as its digits. -/
def carryWord (b : ℕ) : ℕ → List ℕ → List ℕ
  | c, [] => Nat.digits b c
  | c, w :: ws => (w + c) % b :: carryWord b ((w + c) / b) ws

/-- [proved-derived; formal-checked] **A step emits the phase and passes the winding up.** -/
theorem carryWord_cons (b c w : ℕ) (ws : List ℕ) :
    carryWord b c (w :: ws) =
      PhaseCarry.phase b (w + c) :: carryWord b (PhaseCarry.winding b (w + c)) ws := rfl

theorem ofDigits_zipAdd (b : ℕ) :
    ∀ u v : List ℕ, Nat.ofDigits b (zipAdd u v) = Nat.ofDigits b u + Nat.ofDigits b v
  | [], v => by simp [zipAdd]
  | u :: us, [] => by simp [zipAdd]
  | u :: us, v :: vs => by
      simp only [zipAdd, Nat.ofDigits_cons, ofDigits_zipAdd b us vs]
      ring

theorem ofDigits_map_mul (b x : ℕ) :
    ∀ ys : List ℕ, Nat.ofDigits b (ys.map (x * ·)) = x * Nat.ofDigits b ys
  | [] => by simp
  | y :: ys => by
      simp only [List.map_cons, Nat.ofDigits_cons, ofDigits_map_mul b x ys]
      ring

/-- [proved-derived; formal-checked] **The convolution keeps the product of the values.** -/
theorem ofDigits_conv (b : ℕ) :
    ∀ xs ys : List ℕ, Nat.ofDigits b (conv xs ys) = Nat.ofDigits b xs * Nat.ofDigits b ys
  | [], ys => by simp [conv]
  | x :: xs, ys => by
      simp only [conv, ofDigits_zipAdd, ofDigits_map_mul, Nat.ofDigits_cons, ofDigits_conv b xs ys]
      ring

/-- [proved-derived; formal-checked] **The carry cascade keeps the value**: the carried word reads
the word's value plus the carry it started with. -/
theorem carryWord_value {b : ℕ} (hb : 1 < b) :
    ∀ (c : ℕ) (ws : List ℕ), Nat.ofDigits b (carryWord b c ws) = Nat.ofDigits b ws + c
  | c, [] => by simp [carryWord, Nat.ofDigits_digits]
  | c, w :: ws => by
      simp only [carryWord, Nat.ofDigits_cons, carryWord_value hb _ ws]
      have h := Nat.mod_add_div (w + c) b
      rw [mul_add]
      linarith

/-- [proved-derived; formal-checked] **The carried word is a digit word**: every digit lies below
the base. -/
theorem carryWord_lt {b : ℕ} (hb : 1 < b) :
    ∀ (c : ℕ) (ws : List ℕ), ∀ d ∈ carryWord b c ws, d < b
  | c, [] => fun _ hd => Nat.digits_lt_base hb hd
  | c, w :: ws => by
      intro d hd
      simp only [carryWord, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Nat.mod_lt _ (by omega)
      · exact carryWord_lt hb _ ws d hd

/-- [definition] **Encoding in base `b`**: the radix receiver's digit word, least significant
first. -/
def encode (b n : ℕ) : List ℕ := Nat.digits b n

/-- [definition] **Decoding in base `b`**: the value of a digit word. -/
def decode (b : ℕ) (w : List ℕ) : ℕ := Nat.ofDigits b w

/-- [proved-derived; formal-checked] **The consumer equation for the sum**:
`decode_b (carry (encode_b a ⊕ encode_b c)) = a + c`, its digits below `b`. -/
theorem consumer_add {b : ℕ} (hb : 1 < b) (a c : ℕ) :
    decode b (carryWord b 0 (zipAdd (encode b a) (encode b c))) = a + c ∧
      ∀ d ∈ carryWord b 0 (zipAdd (encode b a) (encode b c)), d < b := by
  refine ⟨?_, carryWord_lt hb 0 _⟩
  simp [decode, encode, carryWord_value hb, ofDigits_zipAdd, Nat.ofDigits_digits]

/-- [proved-derived; formal-checked] **The consumer equation for the product**:
`decode_b (carry (encode_b a ∗ encode_b c)) = a · c`, its digits below `b`. -/
theorem consumer_mul {b : ℕ} (hb : 1 < b) (a c : ℕ) :
    decode b (carryWord b 0 (conv (encode b a) (encode b c))) = a * c ∧
      ∀ d ∈ carryWord b 0 (conv (encode b a) (encode b c)), d < b := by
  refine ⟨?_, carryWord_lt hb 0 _⟩
  simp [decode, encode, carryWord_value hb, ofDigits_conv, Nat.ofDigits_digits]

/-- [definition] **The power by repeated convolution**, each factor carried before the next. -/
def powWord (b : ℕ) (xs : List ℕ) : ℕ → List ℕ
  | 0 => [1]
  | e + 1 => carryWord b 0 (conv (powWord b xs e) xs)

/-- [proved-derived; formal-checked] **The consumer equation for the power**:
`decode_b (powWord (encode_b a) e) = a ^ e`, its digits below `b` once `e ≥ 1`. -/
theorem consumer_pow {b : ℕ} (hb : 1 < b) (a : ℕ) :
    ∀ e : ℕ, decode b (powWord b (encode b a) e) = a ^ e
  | 0 => by simp [decode, powWord]
  | e + 1 => by
      have ih := consumer_pow hb a e
      simp only [decode] at ih ⊢
      rw [powWord, carryWord_value hb, ofDigits_conv, ih, add_zero, encode, Nat.ofDigits_digits,
        pow_succ]

/-- [proved-derived; formal-checked] **The consequence square closes alike in any two bases.** -/
theorem consumer_rebase {b b' : ℕ} (hb : 1 < b) (hb' : 1 < b') (a c : ℕ) :
    decode b (carryWord b 0 (conv (encode b a) (encode b c))) =
      decode b' (carryWord b' 0 (conv (encode b' a) (encode b' c))) := by
  rw [(consumer_mul hb a c).1, (consumer_mul hb' a c).1]

/-! ## 2. The carry is the section flux -/

/-- [proved-derived; formal-checked] **The carry a place passes up is its wheel's section flux.**
Over any aeon of the wheel's lift from `0` to the place's total `t`, forward minus backward
crossings of the section `{x | b ∣ x}` equal the winding `⌊t / b⌋` the cascade passes up. -/
theorem carry_is_section_flux {b : ℕ} (hb : 0 < b) (t : ℕ)
    (γ : Aeon (clockLift (Fin 1)) (fun _ => (0 : ℤ)) (fun _ => (t : ℤ))) :
    ((PhaseCarry.winding b t : ℕ) : ℤ) =
      (forwardCrossings (sectionForm (0 : Fin 1) b) γ.steps : ℤ) -
        backwardCrossings (sectionForm (0 : Fin 1) b) γ.steps := by
  rw [signed_count_is_flux (0 : Fin 1) hb γ]
  simp [PhaseCarry.winding]

/-! ## 3. The multiplication table: the map of digit-pair carries -/

/-- [definition] The table's digit of the pair `(x, y)`: the trailing face `x y mod b`. -/
def tableDigit (b x y : ℕ) : ℕ := x * y % b

/-- [definition] The table's carry of the pair `(x, y)`: `⌊x y / b⌋`. -/
def tableCarry (b x y : ℕ) : ℕ := x * y / b

/-- [proved-derived; formal-checked] **A table entry is a ratio with remainder**:
`x y = tableDigit + b · tableCarry`. -/
theorem table_div_rem (b x y : ℕ) : tableDigit b x y + b * tableCarry b x y = x * y :=
  Nat.mod_add_div (x * y) b

/-- [proved-derived; formal-checked] **A row's carries are the phase carries of the rate-`x`
clock**: stepping `y` adds `x` to the product, and the carry advances by exactly the carry of the
two phases (`PhaseCarry.winding_add`), for a digit `x < b`. -/
theorem tableCarry_succ {b x : ℕ} (hb : 0 < b) (hx : x < b) (y : ℕ) :
    tableCarry b x (y + 1) = tableCarry b x y + PhaseCarry.carry b (x * y) x := by
  have h := PhaseCarry.winding_add b (x * y) x hb
  unfold PhaseCarry.winding at h
  unfold tableCarry
  rw [show x * (y + 1) = x * y + x by ring, h, Nat.div_eq_of_lt hx, add_zero]

/-- [proved-derived; formal-checked] **A row's digits repeat with period `b / gcd(x, b)`**: a unit
row (`gcd = 1`) runs through the whole circle, a zero divisor's row closes early. -/
theorem tableDigit_periodic (b x y : ℕ) :
    tableDigit b x (y + b / Nat.gcd x b) = tableDigit b x y := by
  unfold tableDigit
  have h : x * (b / Nat.gcd x b) = x / Nat.gcd x b * b := by
    rw [← Nat.mul_div_assoc x (Nat.gcd_dvd_right x b),
      Nat.div_mul_right_comm (Nat.gcd_dvd_left x b) b]
  rw [mul_add, h, Nat.add_mul_mod_self_right]

/-! ## 4. Provenance: one face, three producers, separated by their jets -/

/-- [definition] **Three producers** of a face from a left operand `a` along the right operand's
clock `k`. -/
inductive Producer
  | add
  | mul
  | pow
  deriving DecidableEq, Repr

namespace Producer

/-- [definition] The face a producer emits at `(a, k)`, read in `ℤ`. -/
def face : Producer → ℕ → ℕ → ℤ
  | add, a, k => (a : ℤ) + k
  | mul, a, k => (a : ℤ) * k
  | pow, a, k => (a : ℤ) ^ k

/-- [definition] **The jet along the right operand's clock**: the face, its first difference and
its second difference. -/
def jet (p : Producer) (a k : ℕ) : ℤ × ℤ × ℤ :=
  (p.face a k, p.face a (k + 1) - p.face a k,
    p.face a (k + 2) - 2 * p.face a (k + 1) + p.face a k)

theorem jet_add (a k : ℕ) : add.jet a k = ((a : ℤ) + k, 1, 0) := by
  simp only [jet, face, Prod.mk.injEq]; push_cast
  exact ⟨trivial, by ring, by ring⟩

theorem jet_mul (a k : ℕ) : mul.jet a k = ((a : ℤ) * k, (a : ℤ), 0) := by
  simp only [jet, face, Prod.mk.injEq]; push_cast
  exact ⟨trivial, by ring, by ring⟩

theorem jet_pow (a k : ℕ) :
    pow.jet a k = ((a : ℤ) ^ k, (a : ℤ) ^ k * (a - 1), (a : ℤ) ^ k * (a - 1) ^ 2) := by
  simp only [jet, face, Prod.mk.injEq]
  exact ⟨trivial, by ring, by ring⟩

end Producer

open Producer

/-- [proved-derived; formal-checked] **One face, three producers**: `2 + 2 = 2 · 2 = 2 ^ 2 = 4`. -/
theorem one_face_three_producers :
    add.face 2 2 = 4 ∧ mul.face 2 2 = 4 ∧ pow.face 2 2 = 4 := by
  norm_num [face]

/-- [proved-derived; formal-checked] **Their jets at `(2, 2)`**: `(4, 1, 0)`, `(4, 2, 0)`,
`(4, 4, 4)`. -/
theorem jets_at_two_two :
    add.jet 2 2 = (4, 1, 0) ∧ mul.jet 2 2 = (4, 2, 0) ∧ pow.jet 2 2 = (4, 4, 4) := by
  rw [jet_add, jet_mul, jet_pow]
  norm_num

/-- [proved-derived; formal-checked] **The jet to second order separates every two producers**
from a left operand `a ≥ 2`: the first difference parts the sum from the product (`1 ≠ a`), and
the second parts the power from both (`0 ≠ a^k (a − 1)²`). -/
theorem jet_separates {a : ℕ} (ha : 2 ≤ a) (k : ℕ) {p q : Producer} (hpq : p ≠ q) :
    p.jet a k ≠ q.jet a k := by
  have ha' : (2 : ℤ) ≤ a := by exact_mod_cast ha
  have hpos : (0 : ℤ) < (a : ℤ) ^ k * ((a : ℤ) - 1) ^ 2 := by
    have : (0 : ℤ) < (a : ℤ) - 1 := by linarith
    positivity
  intro h
  cases p <;> cases q <;> simp only [ne_eq, not_true_eq_false, reduceCtorEq] at hpq <;>
    simp only [jet_add, jet_mul, jet_pow, Prod.mk.injEq] at h
  · linarith [h.2.1]
  · linarith [h.2.2]
  · linarith [h.2.1]
  · linarith [h.2.2]
  · linarith [h.2.2]
  · linarith [h.2.2]

/-- [proved-derived; formal-checked] **The jet to second order separates two producers whatever
their keys**: from left operands `a, a' ≥ 2` and any starts `k, k'`, the first difference parts the
sum from the product (`1 ≠ a'`), and the second parts the power from both
(`0 ≠ a^k (a − 1)²`). So on a faces-only run of one producer, every family of another producer,
whatever keys it holds, dies by the third face (the acceptance run's control, THE_REBUILD U6
item 3). -/
theorem jet_separates_across_keys {a a' : ℕ} (ha : 2 ≤ a) (ha' : 2 ≤ a') (k k' : ℕ)
    {p q : Producer} (hpq : p ≠ q) : p.jet a k ≠ q.jet a' k' := by
  have h2 : (2 : ℤ) ≤ a := by exact_mod_cast ha
  have h2' : (2 : ℤ) ≤ a' := by exact_mod_cast ha'
  have hpos : (0 : ℤ) < (a : ℤ) ^ k * ((a : ℤ) - 1) ^ 2 := by
    have : (0 : ℤ) < (a : ℤ) - 1 := by linarith
    positivity
  have hpos' : (0 : ℤ) < (a' : ℤ) ^ k' * ((a' : ℤ) - 1) ^ 2 := by
    have : (0 : ℤ) < (a' : ℤ) - 1 := by linarith
    positivity
  intro h
  cases p <;> cases q <;> simp only [ne_eq, not_true_eq_false, reduceCtorEq] at hpq <;>
    simp only [jet_add, jet_mul, jet_pow, Prod.mk.injEq] at h
  · linarith [h.2.1]
  · linarith [h.2.2]
  · linarith [h.2.1]
  · linarith [h.2.2]
  · linarith [h.2.2]
  · linarith [h.2.2]

/-- [proved-derived; formal-checked] **The face and the first difference tie the product and the
power only at `(2, 1)`**: for `a ≥ 2`, `a k = a^k` and `a = a^k (a − 1)` hold exactly when
`(a, k) = (2, 1)`. Elsewhere the first order already separates them; there the second order does. -/
theorem mul_pow_first_jet_tie_iff {a : ℕ} (ha : 2 ≤ a) (k : ℕ) :
    ((mul.jet a k).1 = (pow.jet a k).1 ∧ (mul.jet a k).2.1 = (pow.jet a k).2.1) ↔
      (a = 2 ∧ k = 1) := by
  rw [jet_mul, jet_pow]
  constructor
  · rintro ⟨-, h⟩
    -- `h : a = a^k (a − 1)` in `ℤ`
    have ha' : (2 : ℤ) ≤ a := by exact_mod_cast ha
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp only [pow_zero, one_mul] at h
        linarith
      · simp only [pow_one] at h
        have hz : (a : ℤ) * ((a : ℤ) - 2) = 0 := by linear_combination -h
        rcases mul_eq_zero.mp hz with h0 | h2
        · linarith
        · exact ⟨by exact_mod_cast (by linarith : (a : ℤ) = 2), rfl⟩
    · exfalso
      have hpow : (a : ℤ) ^ 2 ≤ (a : ℤ) ^ k := pow_le_pow_right₀ (by linarith) hk
      have h1 : (1 : ℤ) ≤ (a : ℤ) - 1 := by linarith
      have hk0 : (0 : ℤ) ≤ (a : ℤ) ^ k := by positivity
      have hge : (a : ℤ) ^ k ≤ (a : ℤ) ^ k * ((a : ℤ) - 1) := by nlinarith
      nlinarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- [proved-derived; formal-checked] **At `a = 0` the product and the power are one species along
the right operand's clock**: `0 · k = 0 ^ k` for every `k ≥ 1`, so no reading of that clock parts
them. -/
theorem zero_mul_pow_species {k : ℕ} (hk : 1 ≤ k) : mul.face 0 k = pow.face 0 k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp [face]

/-- [proved-derived; formal-checked] **The left operand's clock separates them**: `1 · 2 ≠ 1 ^ 2`. -/
theorem left_clock_separates : mul.face 1 2 ≠ pow.face 1 2 := by
  simp [face]

/-- [proved-derived; formal-checked] **The sum is free fall**: its second difference vanishes. -/
theorem add_free_fall (a k : ℕ) :
    add.face a (k + 2) - 2 * add.face a (k + 1) + add.face a k = 0 := by
  simp [face]; ring

/-- [proved-derived; formal-checked] **The product along its multiplier's clock is free fall**. -/
theorem mul_free_fall (a k : ℕ) :
    mul.face a (k + 2) - 2 * mul.face a (k + 1) + mul.face a k = 0 := by
  simp [face]; ring

/-- [proved-derived; formal-checked] **The power is a dilation by `a` each tick**. -/
theorem pow_boost (a k : ℕ) : pow.face a (k + 1) = a * pow.face a k := by
  simp [face, pow_succ]; ring

/-- [proved-derived; formal-checked] **The sum has no single mode**: no ratio `r` carries
`a + k` to `a + k + 1` at every tick, so its minimal recurrence is the double root `1`. -/
theorem add_no_single_mode (a : ℕ) :
    ¬ ∃ r : ℚ, ∀ k : ℕ, (a : ℚ) + (k + 1) = r * ((a : ℚ) + k) := by
  rintro ⟨r, hr⟩
  have h0 := hr 0
  have h1 := hr 1
  push_cast at h0 h1
  have key : ((a : ℚ) + 2) * a = ((a : ℚ) + 1) * ((a : ℚ) + 1) := by
    calc ((a : ℚ) + 2) * a = (r * ((a : ℚ) + 1)) * a := by rw [← h1]; ring
      _ = ((a : ℚ) + 1) * (r * ((a : ℚ) + 0)) := by ring
      _ = ((a : ℚ) + 1) * ((a : ℚ) + 1) := by rw [← h0]; ring
  nlinarith

/-- [proved-derived; formal-checked] **The product with `a ≠ 0` has no single mode.** -/
theorem mul_no_single_mode {a : ℕ} (ha : a ≠ 0) :
    ¬ ∃ r : ℚ, ∀ k : ℕ, (a : ℚ) * (k + 1) = r * ((a : ℚ) * k) := by
  rintro ⟨r, hr⟩
  have h0 := hr 0
  simp at h0
  exact ha h0

/-! ## 5. Powers of two: locked in bases `2^j`, never in base 10 -/

/-- [proved-derived; formal-checked] **In base `2^j` the digit count of `2^k` is `⌊k/j⌋ + 1`**: the
rate-`1/j` clock locks, one digit every `j` doublings. -/
theorem digits_length_two_pow {j : ℕ} (hj : 0 < j) (k : ℕ) :
    (Nat.digits (2 ^ j) (2 ^ k)).length = k / j + 1 := by
  have hb : 1 < 2 ^ j := Nat.one_lt_two_pow (by omega)
  rw [Nat.length_digits _ _ hb (by positivity)]
  congr 1
  rw [Nat.log_eq_iff (Or.inr ⟨hb, by positivity⟩)]
  constructor
  · rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le k j)
  · rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_mul_div_succ k hj)

/-- [proved-derived; formal-checked] **`2^T ≠ 10^S` for `T ≥ 1`**: five divides every positive
power of ten and no power of two. -/
theorem two_pow_ne_ten_pow {T : ℕ} (hT : 0 < T) (S : ℕ) : 2 ^ T ≠ 10 ^ S := by
  intro h
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · have : 1 < 2 ^ T := Nat.one_lt_two_pow (by omega)
    rw [h] at this
    simp at this
  · have h5 : 5 ∣ 2 ^ T := by
      rw [h]
      exact dvd_pow (by norm_num) (by omega)
    have := (Nat.prime_five.dvd_of_dvd_pow h5)
    omega

/-- The digit count of a nonzero value in base 10 bounds it by powers of ten. -/
theorem ten_pow_bounds {n : ℕ} (hn : n ≠ 0) :
    10 ^ ((Nat.digits 10 n).length - 1) ≤ n ∧ n < 10 ^ (Nat.digits 10 n).length := by
  refine ⟨?_, Nat.lt_base_pow_length_digits (by norm_num)⟩
  have := Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  have hlen : 0 < (Nat.digits 10 n).length := by
    rw [Nat.length_digits 10 n (by norm_num) hn]; omega
  have h10 : 10 ^ (Nat.digits 10 n).length = 10 * 10 ^ ((Nat.digits 10 n).length - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- `x^m (x + m) ≤ x (x + 1)^m`: the binomial's first two terms. -/
theorem pow_mul_add_le (x : ℕ) : ∀ m : ℕ, x ^ m * (x + m) ≤ x * (x + 1) ^ m
  | 0 => by simp
  | m + 1 => by
      have ih := pow_mul_add_le x m
      have step : x ^ (m + 1) * (x + (m + 1)) ≤ x ^ m * (x + m) * (x + 1) := by
        rw [pow_succ]
        nlinarith [Nat.zero_le (x ^ m), Nat.zero_le m]
      calc x ^ (m + 1) * (x + (m + 1)) ≤ x ^ m * (x + m) * (x + 1) := step
        _ ≤ x * (x + 1) ^ m * (x + 1) := Nat.mul_le_mul_right _ ih
        _ = x * (x + 1) ^ (m + 1) := by ring

/-- A ratio of powers bounded by ten for every exponent is one: if `y^m < 10 x^m` and
`x^m < 10 y^m` hold for every `m`, then `x = y` (for `x, y ≥ 1`). -/
theorem eq_of_bounded_ratio {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h₁ : ∀ m, y ^ m < 10 * x ^ m) (h₂ : ∀ m, x ^ m < 10 * y ^ m) : x = y := by
  by_contra hne
  have key : ∀ u v : ℕ, 1 ≤ u → u < v → (∀ m, v ^ m < 10 * u ^ m) → False := by
    intro u v hu huv h
    have hle : ∀ m, (u + 1) ^ m ≤ v ^ m := fun m => Nat.pow_le_pow_left huv m
    have hb := pow_mul_add_le u (10 * u)
    have hm := h (10 * u)
    have hle' := hle (10 * u)
    -- `u^m (11 u) ≤ u (u + 1)^m ≤ u v^m < 10 u u^m`
    have hpos : 0 < u ^ (10 * u) := by positivity
    nlinarith
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key x y hx hlt h₁
  · exact key y x hy hgt h₂

/-- [proved-derived; formal-checked] **The base-10 digit counts of `2^k` never lock**: no period
`T ≥ 1` and carry `S` hold from any tick on. A period would bound `(2^T/10^S)^m` between `1/10` and
`10` for every `m`, forcing `2^T = 10^S`. The rate `log₁₀ 2` is a quasicrystal's
(`Aeon/Clock/CarryWord.never_locks_iff_irrational`), while in base `2^j` it locks. -/
theorem ten_digit_count_never_locks :
    ¬ ∃ T S K : ℕ, 0 < T ∧ ∀ k, K ≤ k →
      (Nat.digits 10 (2 ^ (k + T))).length = (Nat.digits 10 (2 ^ k)).length + S := by
  rintro ⟨T, S, K, hT, hper⟩
  set len : ℕ → ℕ := fun k => (Nat.digits 10 (2 ^ k)).length with hlen
  have hstep : ∀ m, len (K + m * T) = len K + m * S := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hper (K + m * T) (by omega)
      simp only [hlen] at this ih ⊢
      rw [show K + (m + 1) * T = K + m * T + T by ring, this, ih]
      ring
  have hK := ten_pow_bounds (n := 2 ^ K) (by positivity)
  have hd : 1 ≤ len K := by
    simp only [hlen]; rw [Nat.length_digits 10 _ (by norm_num) (by positivity)]; omega
  -- for every `m`, `10^(d + mS − 1) ≤ 2^K (2^T)^m < 10^(d + mS)`
  have hbounds : ∀ m, 10 ^ (len K - 1) * (10 ^ S) ^ m ≤ 2 ^ K * (2 ^ T) ^ m ∧
      2 ^ K * (2 ^ T) ^ m < 10 ^ len K * (10 ^ S) ^ m := by
    intro m
    have hb := ten_pow_bounds (n := 2 ^ (K + m * T)) (by positivity)
    have hl := hstep m
    simp only [hlen] at hl
    rw [hl] at hb
    have e1 : 2 ^ (K + m * T) = 2 ^ K * (2 ^ T) ^ m := by rw [pow_add, ← pow_mul, mul_comm m T]
    have e2 : 10 ^ ((Nat.digits 10 (2 ^ K)).length + m * S - 1) =
        10 ^ ((Nat.digits 10 (2 ^ K)).length - 1) * (10 ^ S) ^ m := by
      rw [← pow_mul, ← pow_add, mul_comm S m]
      congr 1
      simp only [hlen] at hd
      omega
    have e3 : 10 ^ ((Nat.digits 10 (2 ^ K)).length + m * S) =
        10 ^ (Nat.digits 10 (2 ^ K)).length * (10 ^ S) ^ m := by
      rw [← pow_mul, ← pow_add, mul_comm S m]
    rw [e1, e2, e3] at hb
    exact hb
  have h10 : 10 ^ len K = 10 * 10 ^ (len K - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hx : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  have hy : 1 ≤ 10 ^ S := Nat.one_le_pow _ _ (by norm_num)
  have hP : 0 < 10 ^ (len K - 1) := by positivity
  have hQ : 10 ^ (len K - 1) ≤ 2 ^ K ∧ 2 ^ K < 10 * 10 ^ (len K - 1) := by
    simp only [hlen] at h10 ⊢
    rw [← h10]
    exact hK
  apply two_pow_ne_ten_pow hT S
  apply eq_of_bounded_ratio hx hy
  · -- `(10^S)^m < 10 (2^T)^m`
    intro m
    have hX : 0 < (2 ^ T) ^ m := by positivity
    have hlo := (hbounds m).1
    have h1 : 2 ^ K * (2 ^ T) ^ m < 10 ^ (len K - 1) * (10 * (2 ^ T) ^ m) := by
      calc 2 ^ K * (2 ^ T) ^ m < 10 * 10 ^ (len K - 1) * (2 ^ T) ^ m :=
            Nat.mul_lt_mul_of_pos_right hQ.2 hX
        _ = 10 ^ (len K - 1) * (10 * (2 ^ T) ^ m) := by ring
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hlo h1)
  · -- `(2^T)^m < 10 (10^S)^m`
    intro m
    have hhi := (hbounds m).2
    rw [h10] at hhi
    have h1 : 10 ^ (len K - 1) * (2 ^ T) ^ m ≤ 2 ^ K * (2 ^ T) ^ m :=
      Nat.mul_le_mul_right _ hQ.1
    have h2 : 10 ^ (len K - 1) * (2 ^ T) ^ m < 10 ^ (len K - 1) * (10 * (10 ^ S) ^ m) := by
      calc 10 ^ (len K - 1) * (2 ^ T) ^ m ≤ 2 ^ K * (2 ^ T) ^ m := h1
        _ < 10 * 10 ^ (len K - 1) * (10 ^ S) ^ m := hhi
        _ = 10 ^ (len K - 1) * (10 * (10 ^ S) ^ m) := by ring
    exact Nat.lt_of_mul_lt_mul_left h2

/-! ## 6. The holds sheet: the code of `N` computed results that hold -/

/-- [proved-derived; formal-checked] **The holds sheet telescopes**: the Krichevsky–Trofimov faces
of `N` holding results on the two-class sheet `{holds, free}`, `(n + ½)/(n + 1)` at the `n`-th,
multiply to `C(2N, N)/4^N`; their code is `2N − log₂ C(2N, N)` bits. -/
theorem holds_sheet_telescope (N : ℕ) :
    ∏ n ∈ Finset.range N, Holonics.HNN.RegionCounts.ktProb n n 2 =
      (Nat.centralBinom N : ℚ) / 4 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, Holonics.HNN.RegionCounts.ktProb]
    have h : ((N : ℚ) + 1) * ((N + 1).centralBinom : ℚ) = 2 * (2 * N + 1) * (N.centralBinom : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ N
    have hN : ((N : ℚ) + 1) ≠ 0 := by positivity
    have hc : ((N + 1).centralBinom : ℚ) = 2 * (2 * N + 1) * (N.centralBinom : ℚ) / ((N : ℚ) + 1) := by
      rw [eq_div_iff hN, mul_comm]; exact h
    rw [hc]
    push_cast
    field_simp
    ring

section Audit

#print axioms carryWord_value
#print axioms carryWord_lt
#print axioms ofDigits_conv
#print axioms consumer_add
#print axioms consumer_mul
#print axioms consumer_pow
#print axioms consumer_rebase
#print axioms carry_is_section_flux
#print axioms table_div_rem
#print axioms tableCarry_succ
#print axioms tableDigit_periodic
#print axioms one_face_three_producers
#print axioms jets_at_two_two
#print axioms jet_separates
#print axioms jet_separates_across_keys
#print axioms mul_pow_first_jet_tie_iff
#print axioms zero_mul_pow_species
#print axioms left_clock_separates
#print axioms add_free_fall
#print axioms mul_free_fall
#print axioms pow_boost
#print axioms add_no_single_mode
#print axioms mul_no_single_mode
#print axioms digits_length_two_pow
#print axioms two_pow_ne_ten_pow
#print axioms ten_digit_count_never_locks
#print axioms holds_sheet_telescope

end Audit

end Holonics.Mathematics.ArithmeticContract
