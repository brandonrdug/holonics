import ElementaryHolonics.Millennium.GeneralOddPlace

/-!
# GeneralClassCoordinates: square classes as an `𝔽₂`-vector

The descent's classes are integers taken **modulo squares**, so they multiply; the
Selmer calculus is stated additively.  This file supplies the bridge: the coordinates
of a square class.

* **`signCoord`** — one bit for the sign;
* **`primeCoord p`** — one bit for the parity of the `p`-adic valuation.

Both are **square-invariant** and **additive over multiplication**, so together they
present the multiplicative square-class group as an `𝔽₂`-vector space, which is the
form every receiver in this development already speaks:

* the real place is `signCoord d₁ = 0`;
* a good prime is `primeCoord p d₁ = 0` and `primeCoord p d₂ = 0`;
* an odd bad prime dividing one root is `primeCoord p d₁ + primeCoord p d₂ = 0`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralClassCoordinates

open Soma.Holonics.Millennium

/-! ## 1. The two coordinate families -/

/-- The sign bit of a class. -/
def signCoord (d : ℤ) : ZMod 2 := if d < 0 then 1 else 0

/-- The `p`-adic parity bit of a class. -/
def primeCoord (p : ℕ) (d : ℤ) : ZMod 2 := (padicValInt p d : ZMod 2)

/-! ## 2. Additivity over multiplication -/

lemma signCoord_mul {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0) :
    signCoord (d * e) = signCoord d + signCoord e := by
  unfold signCoord
  rcases lt_or_gt_of_ne hd with hd' | hd' <;> rcases lt_or_gt_of_ne he with he' | he'
  · rw [if_pos hd', if_pos he', if_neg (not_lt.mpr (le_of_lt (mul_pos_of_neg_of_neg hd' he')))]
    decide
  · rw [if_pos hd', if_neg (not_lt.mpr (le_of_lt he')),
      if_pos (mul_neg_of_neg_of_pos hd' he')]
    decide
  · rw [if_neg (not_lt.mpr (le_of_lt hd')), if_pos he',
      if_pos (mul_neg_of_pos_of_neg hd' he')]
    decide
  · rw [if_neg (not_lt.mpr (le_of_lt hd')), if_neg (not_lt.mpr (le_of_lt he')),
      if_neg (not_lt.mpr (le_of_lt (mul_pos hd' he')))]
    decide

lemma primeCoord_mul {p : ℕ} [Fact p.Prime] {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0) :
    primeCoord p (d * e) = primeCoord p d + primeCoord p e := by
  unfold primeCoord
  rw [padicValInt.mul hd he]
  push_cast
  ring

/-! ## 3. Square invariance -/

lemma signCoord_sq (c : ℤ) (hc : c ≠ 0) : signCoord (c ^ 2) = 0 := by
  unfold signCoord
  rw [if_neg (not_lt.mpr (sq_nonneg c))]

lemma primeCoord_sq {p : ℕ} [Fact p.Prime] (c : ℤ) (hc : c ≠ 0) :
    primeCoord p (c ^ 2) = 0 := by
  unfold primeCoord
  rw [pow_two, padicValInt.mul hc hc]
  push_cast
  rw [show ((padicValInt p c : ℕ) : ZMod 2) + (padicValInt p c : ZMod 2)
      = 2 * (padicValInt p c : ZMod 2) from by ring]
  rw [show (2 : ZMod 2) = 0 from by decide, zero_mul]

/-- **THE SIGN COORDINATE IS SQUARE-INVARIANT**: two integers in the same rational
square class have the same sign bit. -/
theorem theSignCoordinateIsSquareInvariant {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0)
    (h : Descent.SqCls ((d : ℤ) : ℚ) ((e : ℤ) : ℚ)) :
    signCoord d = signCoord e := by
  obtain ⟨c, hc, hval⟩ := h
  have hdq : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd
  have heq : ((e : ℤ) : ℚ) ≠ 0 := by exact_mod_cast he
  have hcsq : 0 < c ^ 2 := by positivity
  unfold signCoord
  rcases lt_or_gt_of_ne he with he' | he'
  · have hdneg : d < 0 := by
      have heqq : ((e : ℤ) : ℚ) < 0 := by exact_mod_cast he'
      have : ((d : ℤ) : ℚ) < 0 := by rw [hval]; nlinarith
      exact_mod_cast this
    rw [if_pos hdneg, if_pos he']
  · have hdpos : 0 < d := by
      have heqq : (0 : ℚ) < ((e : ℤ) : ℚ) := by exact_mod_cast he'
      have : (0 : ℚ) < ((d : ℤ) : ℚ) := by rw [hval]; nlinarith
      exact_mod_cast this
    rw [if_neg (by omega), if_neg (by omega)]


/-- **THE PRIME COORDINATE IS SQUARE-INVARIANT**: two integers in the same rational
square class have the same `p`-adic parity bit.  The scaling factor is a **rational**
square, so its valuation contributes an even amount and dies mod two. -/
theorem thePrimeCoordinateIsSquareInvariant {p : ℕ} [Fact p.Prime] {d e : ℤ}
    (hd : d ≠ 0) (he : e ≠ 0)
    (h : Descent.SqCls ((d : ℤ) : ℚ) ((e : ℤ) : ℚ)) :
    primeCoord p d = primeCoord p e := by
  obtain ⟨c, hc, hval⟩ := h
  have hdq : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd
  have heq : ((e : ℤ) : ℚ) ≠ 0 := by exact_mod_cast he
  -- the rational valuations differ by twice the scaling factor's
  have hvd : padicValRat p ((d : ℤ) : ℚ)
      = 2 * padicValRat p c + padicValRat p ((e : ℤ) : ℚ) := by
    rw [hval, padicValRat.mul (pow_ne_zero 2 hc) heq, padicValRat.pow hc]
    norm_num
  -- and integer valuations are the rational ones
  have hid : padicValRat p ((d : ℤ) : ℚ) = (padicValInt p d : ℤ) := by
    simpa using (padicValRat.of_int (p := p) (z := d))
  have hie : padicValRat p ((e : ℤ) : ℚ) = (padicValInt p e : ℤ) := by
    simpa using (padicValRat.of_int (p := p) (z := e))
  rw [hid, hie] at hvd
  -- so the two integer valuations agree modulo two
  unfold primeCoord
  have hcong : ((padicValInt p d : ℤ)) - ((padicValInt p e : ℤ))
      = 2 * padicValRat p c := by omega
  have hmod : ((padicValInt p d : ℕ) : ZMod 2) - ((padicValInt p e : ℕ) : ZMod 2)
      = 0 := by
    have hcast : (((padicValInt p d : ℤ) - (padicValInt p e : ℤ) : ℤ) : ZMod 2)
        = ((2 * padicValRat p c : ℤ) : ZMod 2) := by rw [hcong]
    push_cast at hcast
    rw [show ((2 : ZMod 2)) = 0 from by decide, zero_mul] at hcast
    exact hcast
  have := sub_eq_zero.mp hmod
  exact this

/-! ## 4. The receivers, in coordinates

Each place's condition is now a linear equation over `𝔽₂` in the coordinates of the
class pair, which is the form `SelmerCalculus` consumes. -/

/-- The real place, in coordinates: the first class has sign bit zero. -/
def realCondition (d₁ : ℤ) : Prop := signCoord d₁ = 0

/-- A good prime, in coordinates: both classes have parity bit zero. -/
def goodCondition (p : ℕ) (d₁ d₂ : ℤ) : Prop :=
  primeCoord p d₁ = 0 ∧ primeCoord p d₂ = 0

/-- An odd bad prime dividing one root, in coordinates: the two parity bits agree. -/
def oddBadCondition (p : ℕ) (d₁ d₂ : ℤ) : Prop :=
  primeCoord p d₁ + primeCoord p d₂ = 0

/-- **THE COORDINATES ARE A HOMOMORPHISM OF SQUARE CLASSES**: sign and parity bits are
additive over multiplication and blind to squares, so the multiplicative square-class
group presents as an `𝔽₂`-vector space — the form every receiver above already
speaks. -/
theorem theCoordinatesArePresentTheClassGroupOverTwo {p : ℕ} [Fact p.Prime]
    {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0) (c : ℤ) (hc : c ≠ 0) :
    signCoord (d * e) = signCoord d + signCoord e ∧
    primeCoord p (d * e) = primeCoord p d + primeCoord p e ∧
    signCoord (c ^ 2) = 0 ∧ primeCoord p (c ^ 2) = 0 :=
  ⟨signCoord_mul hd he, primeCoord_mul hd he, signCoord_sq c hc, primeCoord_sq c hc⟩

end Soma.Holonics.Millennium.GeneralClassCoordinates
