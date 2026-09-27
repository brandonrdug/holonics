import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

/-!
# The radix window: a residue read after an exact scaling

[definition] The window of `l` digits in radix `b` at offset `k` of a real `x` is
`window b k l x = ⌊bᵏ⁺ˡ x⌋ mod bˡ`: a receiver face read after the exact scaling `bᵏ⁺ˡ`, with the
integer floor retained until the final, declared residue (`window`, `scaledWindow`).

[proved-derived; formal-checked] What is proved.

1. **An enclosure certifies a window by the floors of its ends.** If `L ≤ x ≤ U` and the scaled
   floors of both ends agree, the scaled floor of `x` is theirs
   (`floor_scaled_eq_of_endpoint_floors_eq`), and the window is its residue
   (`window_eq_of_endpoint_floors_eq`).
2. **Windows are translation and offset readings.** A scaled window ignores integer translation
   (`scaledWindow_int_translate`), reads the fractional part (`scaledWindow_eq_fract_floor`,
   `scaledWindow_eq_fract_floor_of_pos`), and a window at offset `k` is the scaled window of
   `bᵏ x` (`window_eq_scaledWindow`).

[counterexample; formal-checked] **Residues alone do not certify**
(`endpoint_residue_agreement_wraparound`): `9` and `19` share the residue `9 mod 10` and differ,
so two enclosure ends whose scaled floors agree only modulo `bˡ` can straddle a carry; the
certificate compares the floors themselves.

[proved-derived; formal-checked] **The digit faces of an integer** (§ Digit faces). An integer is a
digit vector, and its faces are residues read through the radix.
3. **Multiplication is convolution with carry.** The value of the convolution of two digit vectors
   is the product of their values (`digit_product_is_carry_of_convolution`, through
   `Polynomial.coeff_mul` and `Polynomial.eval_mul`); one carry step keeps the value
   (`carry_step_value`), so the carried word of the convolution is the product's digits, the unique
   word with digits below `b` and a nonzero leading digit (`carried_word_is_product_digits`).
4. **A prime is a grating on the digit index.** With the low `m` digits fixed at `r` and the upper
   part `k`, a prime `p ∤ b` divides `bᵐ k + r` exactly on one residue class of `k`,
   `k ≡ −r (bᵐ)⁻¹` in `ZMod p` (`grating_on_digit_index`).
5. **The cheap faces** (`cheap_faces`): for `d ∣ b` the last digit, for `d ∣ b − 1` the digit sum,
   and for `d ∣ b + 1` the alternating digit sum are congruent to `n` modulo `d`.

Consumers: `Compression/Landmark/ConstraintIdentity` (certified windows of π and `e`).
-/

noncomputable section

namespace Holonics.Mathematics.RadixWindowReceiver

def window (b k l : ℕ) (x : ℝ) : ℤ :=
  ⌊(b : ℝ) ^ (k + l) * x⌋ % (b ^ l : ℤ)

def scaledWindow (b l : ℕ) (y : ℝ) : ℤ :=
  ⌊(b : ℝ) ^ l * y⌋ % (b ^ l : ℤ)

theorem floor_scaled_eq_of_endpoint_floors_eq
    {b k l : ℕ} (hb : 0 < b) {L U x : ℝ} {K : ℤ}
    (hLU : L ≤ x) (hxU : x ≤ U)
    (hL : ⌊(b : ℝ) ^ (k + l) * L⌋ = K)
    (hU : ⌊(b : ℝ) ^ (k + l) * U⌋ = K) :
    ⌊(b : ℝ) ^ (k + l) * x⌋ = K := by
  have hs : 0 < (b : ℝ) ^ (k + l) := by positivity
  have hLx : (b : ℝ) ^ (k + l) * L ≤ (b : ℝ) ^ (k + l) * x :=
    mul_le_mul_of_nonneg_left hLU hs.le
  have hxU' : (b : ℝ) ^ (k + l) * x ≤ (b : ℝ) ^ (k + l) * U :=
    mul_le_mul_of_nonneg_left hxU hs.le
  have hfloorL : K ≤ ⌊(b : ℝ) ^ (k + l) * x⌋ := by
    rw [← hL]
    exact Int.floor_mono hLx
  have hfloorU : ⌊(b : ℝ) ^ (k + l) * x⌋ ≤ K := by
    rw [← hU]
    exact Int.floor_mono hxU'
  exact le_antisymm hfloorU hfloorL

theorem window_eq_of_endpoint_floors_eq
    {b k l : ℕ} (hb : 0 < b) {L U x : ℝ} {K : ℤ}
    (hLU : L ≤ x) (hxU : x ≤ U)
    (hL : ⌊(b : ℝ) ^ (k + l) * L⌋ = K)
    (hU : ⌊(b : ℝ) ^ (k + l) * U⌋ = K) :
    window b k l x = K % (b ^ l : ℤ) := by
  unfold window
  rw [floor_scaled_eq_of_endpoint_floors_eq hb hLU hxU hL hU]

theorem scaledWindow_int_translate (b l : ℕ) (y : ℝ) (j : ℤ) :
    scaledWindow b l (y + j) = scaledWindow b l y := by
  unfold scaledWindow
  have hpow : ((b : ℝ) ^ l) * (j : ℝ) = ((b ^ l : ℤ) * j : ℤ) := by
    norm_num
  rw [mul_add, hpow, Int.floor_add_intCast]
  exact Int.add_mul_emod_self_left _ _ _

theorem scaledWindow_eq_fract_floor (b l : ℕ) (y : ℝ) :
    scaledWindow b l y =
      ⌊(b : ℝ) ^ l * Int.fract y⌋ % (b ^ l : ℤ) := by
  unfold scaledWindow
  have hpow : ((b : ℝ) ^ l) * (Int.floor y : ℝ) =
      ((b ^ l : ℤ) * Int.floor y : ℤ) := by
    norm_num
  have hy : y = Int.fract y + (Int.floor y : ℝ) := by
    change y = (y - (Int.floor y : ℝ)) + (Int.floor y : ℝ)
    ring
  conv_lhs =>
    rw [hy, mul_add, hpow, Int.floor_add_intCast]
  exact Int.add_mul_emod_self_left _ _ _

theorem scaledWindow_eq_fract_floor_of_pos (b l : ℕ) (hb : 0 < b) (y : ℝ) :
    scaledWindow b l y = ⌊(b : ℝ) ^ l * Int.fract y⌋ := by
  rw [scaledWindow_eq_fract_floor]
  apply Int.emod_eq_of_lt
  · positivity
  · have hs : 0 < (b : ℝ) ^ l := by positivity
    have hlt : Int.fract y < 1 := Int.fract_lt_one y
    have hreal : (b : ℝ) ^ l * Int.fract y < (b : ℝ) ^ l :=
      by simpa using (mul_lt_mul_of_pos_left hlt hs)
    rw [Int.floor_lt]
    exact_mod_cast hreal

theorem window_eq_scaledWindow (b k l : ℕ) (x : ℝ) :
    window b k l x = scaledWindow b l ((b : ℝ) ^ k * x) := by
  unfold window scaledWindow
  congr 2
  rw [pow_add]
  ring

/-- [counterexample; formal-checked] Equal residues, different floors: `9 ≡ 19 (mod 10)`. -/
theorem endpoint_residue_agreement_wraparound :
    ((9 : ℤ) % (10 : ℤ)) = ((19 : ℤ) % (10 : ℤ)) ∧ (9 : ℤ) ≠ 19 := by
  norm_num

/-! ## Digit faces: convolution with carry, prime gratings, and cheap residues -/

open Finset in
/-- [proved-derived; formal-checked] **`digit_product_is_carry_of_convolution`.** Two digit vectors
`x`, `y` (the coefficient vectors of `x y : ℕ[X]`) at base `b`: the convolution
`c_k = Σ_(i+j=k) x_i y_j` has value `Σ c_k bᵏ = (Σ x_i bⁱ)(Σ y_j bʲ)`. -/
theorem digit_product_is_carry_of_convolution (x y : Polynomial ℕ) (b : ℕ) :
    (∑ k ∈ range ((x * y).natDegree + 1),
        (∑ ij ∈ antidiagonal k, x.coeff ij.1 * y.coeff ij.2) * b ^ k) =
      (∑ i ∈ range (x.natDegree + 1), x.coeff i * b ^ i) *
        (∑ j ∈ range (y.natDegree + 1), y.coeff j * b ^ j) := by
  simp_rw [← Polynomial.coeff_mul]
  rw [← Polynomial.eval_eq_sum_range, ← Polynomial.eval_eq_sum_range,
    ← Polynomial.eval_eq_sum_range, Polynomial.eval_mul]

/-- [proved-derived; formal-checked] **One carry step keeps the value**: the digit `c₀` keeps its
residue `c₀ mod b` and passes `⌊c₀/b⌋` to the next place. -/
theorem carry_step_value (b c₀ c₁ : ℕ) (rest : List ℕ) :
    Nat.ofDigits b (c₀ :: c₁ :: rest) = Nat.ofDigits b (c₀ % b :: (c₁ + c₀ / b) :: rest) := by
  simp only [Nat.ofDigits_cons]
  conv_lhs => rw [← Nat.mod_add_div c₀ b]
  ring

/-- [proved-derived; formal-checked] **The carried word is the product's digits.** A word with
every digit below `b` and a nonzero leading digit whose value is the convolution's value is the
base-`b` digit word of the product. -/
theorem carried_word_is_product_digits (x y : Polynomial ℕ) {b : ℕ} (hb : 1 < b) (L : List ℕ)
    (hdigit : ∀ l ∈ L, l < b) (hlead : ∀ h : L ≠ [], L.getLast h ≠ 0)
    (hvalue : Nat.ofDigits b L = (x * y).eval b) :
    L = Nat.digits b (x.eval b * y.eval b) := by
  rw [← Polynomial.eval_mul, ← hvalue, Nat.digits_ofDigits b hb L hdigit hlead]

/-- [proved-derived; formal-checked] **`grating_on_digit_index`.** For a prime `p ∤ b`, the numbers
`bᵐ k + r` (upper part `k`, low digits `r`) divisible by `p` are exactly one residue class of the
upper part: `k ≡ −r (bᵐ)⁻¹` in `ZMod p`. -/
theorem grating_on_digit_index {p : ℕ} (hp : p.Prime) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) (m : ℕ)
    (k r : ℤ) :
    (p : ℤ) ∣ b ^ m * k + r ↔ (k : ZMod p) = -(r : ZMod p) * ((b : ZMod p) ^ m)⁻¹ := by
  have := Fact.mk hp
  have hb' : (b : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hu : (b : ZMod p) ^ m ≠ 0 := pow_ne_zero m hb'
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- [proved-derived; formal-checked] **`cheap_faces`.** Modulo a divisor of `b`, `n` is its last
digit `n mod b`; modulo a divisor of `b − 1`, its digit sum; modulo a divisor of `b + 1`, its
alternating digit sum. -/
theorem cheap_faces (b d n : ℕ) :
    ((d : ℤ) ∣ b → (n : ℤ) ≡ ((n % b : ℕ) : ℤ) [ZMOD d]) ∧
      ((d : ℤ) ∣ (b : ℤ) - 1 → (n : ℤ) ≡ (((Nat.digits b n).sum : ℕ) : ℤ) [ZMOD d]) ∧
      ((d : ℤ) ∣ (b : ℤ) + 1 →
        (n : ℤ) ≡ ((Nat.digits b n).map fun l : ℕ => (l : ℤ)).alternatingSum [ZMOD d]) := by
  refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
  · rw [Int.natCast_mod]
    exact ((Int.mod_modEq (n : ℤ) b).symm).of_dvd hd
  · have h1 : (b : ℤ) ≡ 1 [ZMOD d] := (Int.modEq_iff_dvd.mpr hd).symm
    have := Nat.zmodeq_ofDigits_digits d b 1 h1 n
    rwa [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, ← Nat.coe_ofDigits, Nat.ofDigits_one] at this
  · have h1 : (b : ℤ) ≡ -1 [ZMOD d] :=
      (Int.modEq_iff_dvd.mpr (by rwa [sub_neg_eq_add])).symm
    have := Nat.zmodeq_ofDigits_digits d b (-1) h1 n
    rwa [Nat.ofDigits_neg_one] at this

end Holonics.Mathematics.RadixWindowReceiver
