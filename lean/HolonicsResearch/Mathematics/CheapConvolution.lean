import HolonicsResearch.Mathematics.ArithmeticContract
import HolonicsResearch.Mathematics.BaseAction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The cheap rings collapse the digit convolution, and a face is read leading first by the fold

The record `research/records/2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md`
(§§1, 3 and 6; atlas `radix.cheap-ring-path-collapse`, `radix.held-face-reading-order`) reads a
product on the base's cheap rings: where the base reads `1` (`q ∣ b − 1`) or `−1` (`q ∣ b + 1`),
every path of the digit convolution lands in phase, so the product's face is one crossing of the
operands' faces and the carries drop out; and a word's face on `ℤ/q` is read leading first by the
fold `x ↦ b x + d`. #410 owes these; this file proves them over any commutative ring, so over every
`ZMod q`.

[proved-derived; formal-checked] What is proved.

1. **A word's face where the base reads `1` is its digit sum** (`cast_ofDigits_of_one`), and
   **where it reads `−1`, its alternating sum** (`altSum`, `cast_ofDigits_of_neg_one`):
   `Σ_k d_k bᵏ = Σ_k d_k` and `Σ_k (−1)ᵏ d_k` in the ring.
2. **The convolution collapses** (`conv_face_of_one`, `conv_face_of_neg_one`, `conv_sum`): with
   `c = conv x y` (`ArithmeticContract.conv`, `c_k = Σ_(i+j=k) x_i y_j` before carry),
   `Σ_k c_k bᵏ = (Σ_i x_i)(Σ_j y_j)` where `b` reads `1` and `(Σ_i (−1)ⁱ x_i)(Σ_j (−1)ʲ y_j)`
   where it reads `−1`; over `ℕ` the coefficients sum to the product of the sums.
3. **The carries drop out** (`carry_drops_out_of_one`, `carry_drops_out_of_neg_one`,
   `carried_product_face_of_one`, `carried_product_face_of_neg_one`): the carry cascade keeps the
   value (`ArithmeticContract.carryWord_value`), so on a cheap ring the carried word's digit
   (alternating) sum is the uncarried one's, and the carried product's face is the product of the
   operands' faces. In base 10 this is the 9-face and the 11-face (`nine_face`, `eleven_face`).
4. **Leading first is the fold** (`foldl_digitMove`, `ofDigits_eq_fold`, `face_is_fold`): over
   any commutative ring, reading the word from its leading digit by `x ↦ b x + d`
   (`BaseAction.digitMove`) from `a` gives `a bⁿ + Σ_k d_k bᵏ`; from `0` it is the word's value,
   and on `ℤ/q` it is `n mod q` for the base-`b` digits of `n`.

Owed (#410): the chain-rule statement that a held face's gain `I(W; q | F)` is the same in every
reading order of the places.

The computational object is the helical pair interaction: the convolution pairs digit `i` with digit
`j` at place `i + j`, and on a cheap ring every pair lands in phase. Of the winding guide's six
general objects this touches the helix (the carry cascade) and the pair (the convolution); faces
and placement, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas rows `radix.cheap-ring-path-collapse` and `radix.held-face-reading-order`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.CheapConvolution

open Holonics.Mathematics.ArithmeticContract Holonics.Mathematics.BaseAction

variable {R : Type*} [CommRing R]

/-- [definition] The alternating digit sum `Σ_k (−1)ᵏ d_k` of a word, least significant first. -/
def altSum : List ℕ → R
  | [] => 0
  | d :: L => (d : R) - altSum L

/-- [proved-derived; formal-checked] **Where the base reads `1`, a word's face is its digit
sum.** -/
theorem cast_ofDigits_of_one {b : ℕ} (hb : (b : R) = 1) (L : List ℕ) :
    ((Nat.ofDigits b L : ℕ) : R) = ((L.sum : ℕ) : R) := by
  induction L with
  | nil => simp
  | cons d L ih =>
    simp only [Nat.ofDigits_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, hb, one_mul, ih]

/-- [proved-derived; formal-checked] **Where the base reads `−1`, a word's face is its alternating
sum.** -/
theorem cast_ofDigits_of_neg_one {b : ℕ} (hb : (b : R) = -1) (L : List ℕ) :
    ((Nat.ofDigits b L : ℕ) : R) = altSum L := by
  induction L with
  | nil => simp [altSum]
  | cons d L ih =>
    simp only [Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul, hb, ih, altSum]
    ring

/-- [proved-derived; formal-checked] **The convolution collapses where the base reads `1`:**
`Σ_k c_k bᵏ = (Σ_i x_i)(Σ_j y_j)`. -/
theorem conv_face_of_one {b : ℕ} (hb : (b : R) = 1) (xs ys : List ℕ) :
    ((Nat.ofDigits b (conv xs ys) : ℕ) : R) = ((xs.sum : ℕ) : R) * ((ys.sum : ℕ) : R) := by
  rw [ofDigits_conv, Nat.cast_mul, cast_ofDigits_of_one hb, cast_ofDigits_of_one hb]

/-- [proved-derived; formal-checked] **The convolution collapses where the base reads `−1`:**
`Σ_k c_k bᵏ = (Σ_i (−1)ⁱ x_i)(Σ_j (−1)ʲ y_j)`. -/
theorem conv_face_of_neg_one {b : ℕ} (hb : (b : R) = -1) (xs ys : List ℕ) :
    ((Nat.ofDigits b (conv xs ys) : ℕ) : R) = altSum xs * altSum ys := by
  rw [ofDigits_conv, Nat.cast_mul, cast_ofDigits_of_neg_one hb, cast_ofDigits_of_neg_one hb]

/-- [proved-derived; formal-checked] The convolution's coefficients sum to the product of the
operands' sums. -/
theorem conv_sum (xs ys : List ℕ) : (conv xs ys).sum = xs.sum * ys.sum := by
  have h := ofDigits_conv 1 xs ys
  rwa [Nat.ofDigits_one, Nat.ofDigits_one, Nat.ofDigits_one] at h

/-- [proved-derived; formal-checked] **The carries drop out where the base reads `1`:** the carried
word's digit sum is the uncarried word's. -/
theorem carry_drops_out_of_one {b : ℕ} (hb1 : 1 < b) (hb : (b : R) = 1) (w : List ℕ) :
    (((carryWord b 0 w).sum : ℕ) : R) = ((w.sum : ℕ) : R) := by
  rw [← cast_ofDigits_of_one hb, ← cast_ofDigits_of_one hb, carryWord_value hb1, add_zero]

/-- [proved-derived; formal-checked] **The carries drop out where the base reads `−1`.** -/
theorem carry_drops_out_of_neg_one {b : ℕ} (hb1 : 1 < b) (hb : (b : R) = -1) (w : List ℕ) :
    (altSum (carryWord b 0 w) : R) = altSum w := by
  rw [← cast_ofDigits_of_neg_one hb, ← cast_ofDigits_of_neg_one hb, carryWord_value hb1, add_zero]

/-- [proved-derived; formal-checked] **The carried product's face is the product of the operands'
faces** where the base reads `1`. -/
theorem carried_product_face_of_one {b : ℕ} (hb1 : 1 < b) (hb : (b : R) = 1) (xs ys : List ℕ) :
    (((carryWord b 0 (conv xs ys)).sum : ℕ) : R) = ((xs.sum : ℕ) : R) * ((ys.sum : ℕ) : R) := by
  rw [carry_drops_out_of_one hb1 hb, ← cast_ofDigits_of_one hb, conv_face_of_one hb]

/-- [proved-derived; formal-checked] **The carried product's face is the product of the operands'
faces** where the base reads `−1`. -/
theorem carried_product_face_of_neg_one {b : ℕ} (hb1 : 1 < b) (hb : (b : R) = -1)
    (xs ys : List ℕ) :
    (altSum (carryWord b 0 (conv xs ys)) : R) = altSum xs * altSum ys := by
  rw [carry_drops_out_of_neg_one hb1 hb, ← cast_ofDigits_of_neg_one hb, conv_face_of_neg_one hb]

/-- [proved-standard; formal-checked] Ten reads `1` on ring 9. -/
theorem ten_on_nine : ((10 : ℕ) : ZMod 9) = 1 := by decide

/-- [proved-standard; formal-checked] Ten reads `−1` on ring 11. -/
theorem ten_on_eleven : ((10 : ℕ) : ZMod 11) = -1 := by decide

/-- [proved-derived; formal-checked] **The 9-face of a carried base-10 product** is the product of
the operands' digit sums. -/
theorem nine_face (xs ys : List ℕ) :
    (((carryWord 10 0 (conv xs ys)).sum : ℕ) : ZMod 9) =
      ((xs.sum : ℕ) : ZMod 9) * ((ys.sum : ℕ) : ZMod 9) :=
  carried_product_face_of_one (by norm_num) ten_on_nine xs ys

/-- [proved-derived; formal-checked] **The 11-face of a carried base-10 product** is the product of
the operands' alternating sums. -/
theorem eleven_face (xs ys : List ℕ) :
    (altSum (carryWord 10 0 (conv xs ys)) : ZMod 11) = altSum xs * altSum ys :=
  carried_product_face_of_neg_one (by norm_num) ten_on_eleven xs ys

/-- [proved-standard; formal-checked] **Reading leading first is the fold `x ↦ b x + d`:** from
`a`, the fold over the reversed (least-significant-first) word gives `a bⁿ + Σ_k d_k bᵏ`. -/
theorem foldl_digitMove (b a : R) (L : List ℕ) :
    L.reverse.foldl (fun x d => digitMove b (d : R) x) a = a * b ^ L.length + Nat.ofDigits b L := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons d L ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, digitMove, Nat.ofDigits, List.length_cons,
      pow_succ]
    ring

/-- [proved-standard; formal-checked] From rest the fold reads the word's value. -/
theorem ofDigits_eq_fold (b : R) (L : List ℕ) :
    Nat.ofDigits b L = L.reverse.foldl (fun x d => digitMove b (d : R) x) 0 := by
  rw [foldl_digitMove]
  ring

/-- [proved-standard; formal-checked] **A number's face on a ring is the leading-first fold of its
base-`b` digits.** -/
theorem face_is_fold (b n : ℕ) :
    (n : R) = (Nat.digits b n).reverse.foldl (fun x d => digitMove (b : R) (d : R) x) 0 := by
  conv_lhs => rw [← Nat.ofDigits_digits b n]
  rw [Nat.coe_ofDigits, ofDigits_eq_fold]

end Holonics.Mathematics.CheapConvolution
