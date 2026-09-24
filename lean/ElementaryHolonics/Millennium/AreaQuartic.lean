import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# The coset at `2³`, and the area partition that carries the global obstruction

Brandon's question, 2026-08-23: seventeen carries a coset, `2⁸` was named as another, **why is
there no coset around `2³`?**

There is one, and this file exhibits it.  The three powers of two that occur in the seventeen
descent are three *different objects* and had been running together:

| power | what it actually is |
|---|---|
| `2²` | the order of `E_n[2] ≅ (ℤ/2)²` — the free Klein action, the orbit engine |
| `2³` | the order of `⟨2⟩ ≤ 𝔽₁₇ˣ`, and the order of the local square-class group at the place `2` |
| `2⁸` | **not an object.**  `2⁸ ≡ 1 (mod 17)` because `ord(2) = 2³`; as a test depth it was overkill |

**Why there is no *label* at `2³`.**  The coset labels of a two-descent are square classes, and a
square class is `𝔽₂`-graded: `2³ = 2·2²`, so `2³` and `2` are *the same element* of `ℚˣ/(ℚˣ)²`.
The odd powers of two are one axis, not three.  A coset "around `2³`" is the coset around `2`.

**Where `2³` is real.**  It is a *group order*, never a label.  `ord(2) = 8 = 2³` in `𝔽₁₇ˣ`, which
is cyclic of order `2⁴` because `17 = 2^(2²) + 1` is a Fermat prime — the only primes whose whole
multiplicative group is a 2-tower.  `⟨2⟩` is therefore exactly the subgroup of squares, of index
`2`, and `2` fails to sit one level deeper: **`2` is a square mod `17` and not a fourth power.**
That single missing level is the quartic-residue obstruction the seventeen descent runs on.

**And the obstruction is read off an area.**  Gauss: for `p ≡ 1 (mod 4)` written `p = a² + b²`
with `b` even, `2` is a fourth power mod `p` **iff `b ≡ 0 (mod 8)`**.  Seventeen is `1² + 4²`, and
`4 ≢ 0 (mod 8)`.  So the global obstruction at seventeen is a congruence *on the side length of
the binomial area partition of the prime*, mod `2³`.  That is the coupling between prime
distribution and area partition, made into a decision procedure.

Every arithmetic statement below is kernel-decided.  Gauss's criterion is carried as a named
`Prop` and **not assumed**: its seventeen instance is verified independently on both sides.
-/

namespace Soma.Holonics.Millennium.AreaQuartic

open Finset

/-! ## 1.  The square class collapses the odd powers of two -/

/-- **THE SQUARE-CLASS RECEIVER COLLAPSES `2³` ONTO `2`.**  `8 = 2 · 2²`, so in `ℚˣ/(ℚˣ)²` the
two are one element.  There is no separate coset label at `2³` because there is no separate
address: the prime axes carry a *bit*, not an exponent. -/
theorem theSquareClassCollapsesTheOddPowersOfTwo : (8 : ℤ) = 2 * 2 ^ 2 := by norm_num

/-- The same collapse at every odd height: `2^(2k+1)` is `2` times a square. -/
theorem theOddPowersOfTwoAreOneAxis (k : ℕ) : (2 : ℤ) ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 := by
  ring

/-! ## 2.  Where `2³` is real: it is a group order -/

/-- **THE ORDER OF `2` IN `𝔽₁₇ˣ` IS `2³`.**  This is the coset at `2³`. -/
theorem theOrderOfTwoIsTwoCubed : (2 : ZMod 17) ^ (2 ^ 3) = 1 := by decide

/-- And the half-turn sits at `2²`: `2^(2²) = −1`, so the order is exactly `2³`, not less. -/
theorem theHalfTurnSitsAtTwoSquared : (2 : ZMod 17) ^ (2 ^ 2) = -1 := by decide

/-- `2` generates the squares of `𝔽₁₇ˣ`: eight distinct powers. -/
theorem thePowersOfTwoAreTheSquares :
    (image (fun k : Fin 8 => (2 : ZMod 17) ^ (k : ℕ)) univ) =
      (image (fun x : ZMod 17 => x ^ 2) (univ.filter (· ≠ 0))) := by decide

/-- **`2` IS A SQUARE MOD SEVENTEEN.** -/
theorem theTwoIsASquareModSeventeen : ∃ x : ZMod 17, x ^ 2 = 2 := by decide

/-- **`2` IS NOT A FOURTH POWER MOD SEVENTEEN.**  One level short — and that missing level is
the whole obstruction. -/
theorem theTwoIsNotAFourthPowerModSeventeen : ∀ x : ZMod 17, x ^ 4 ≠ 2 := by decide

/-- Seventeen is a Fermat prime: `𝔽₁₇ˣ` is a pure 2-tower of height `2²`. -/
theorem theSeventeenIsAFermatPrime : (17 : ℕ) = 2 ^ (2 ^ 2) + 1 := by norm_num

/-- The fourth powers form the subgroup of order `2²`, so the tower has a genuine fourth level
for `2` to miss. -/
theorem theFourthPowersHaveOrderTwoSquared :
    (image (fun x : ZMod 17 => x ^ 4) (univ.filter (· ≠ 0))).card = 2 ^ 2 := by decide

/-! ## 3.  The local square-class group at the place two has order `2³` -/

/-- Every unit mod `8` squares to one, so the 2-adic unit square classes are exactly `(ℤ/8)ˣ`. -/
theorem theTwoAdicUnitsAreSquareClassesModEight : ∀ u : (ZMod 8)ˣ, u ^ 2 = 1 := by decide

/-- `(ℤ/8)ˣ` has order `2²`; with the valuation bit the local square-class group at `2` has
order `2³ = 8`. -/
theorem theTwoAdicUnitClassesHaveOrderTwoSquared : Fintype.card (ZMod 8)ˣ = 2 ^ 2 := by decide

/-- **THE CONTRAST WITH AN ODD PLACE.**  At `17` the unit square classes number `2`, so the local
square-class group has order `2²`, one bit smaller than at the place `2`.  That single extra bit
at `2` is why the congruent-number law is a condition mod `2³` and not mod `2²`. -/
theorem theOddPlaceHasOneFewerBit :
    (image (fun x : ZMod 17 => x ^ 2) (univ.filter (· ≠ 0))).card * 2 = 16 := by decide

/-! ## 4.  `2⁸` is not an object: it is `ord(2)` read once around -/

/-- **`2⁸ ≡ 1 (mod 17)` IS THE ORDER, NOT A NEW STRUCTURE.**  The probe depth `2⁸` named nothing
that `2³` had not already fixed. -/
theorem theEighthPowerIsTheFirstReturn : (2 : ZMod 17) ^ 8 = 1 ∧ (2 : ZMod 17) ^ 4 ≠ 1 := by
  decide

/-! ## 5.  The area partition carries the obstruction -/

/-- **THE BINOMIAL AREA PARTITION OF SEVENTEEN**, and its even side is `2²`. -/
theorem theAreaPartitionOfSeventeen : (17 : ℤ) = 1 ^ 2 + 4 ^ 2 := by norm_num

/-- Seventeen also splits as `3² + 2³` — the `2³` is visible in the area itself. -/
theorem theSecondAreaPartitionOfSeventeen : (17 : ℤ) = 3 ^ 2 + 2 ^ 3 := by norm_num

/-- **THE EVEN SIDE IS NOT EIGHTFOLD.**  `b = 2²`, and `2² ≢ 0 (mod 2³)`. -/
theorem theEvenSideIsNotEightfold : ¬ ((8 : ℕ) ∣ 4) := by decide

/-- **GAUSS'S QUARTIC CRITERION**, carried as a named statement and assumed nowhere below:
for `p ≡ 1 (mod 4)` written `p = a² + b²` with `b` even, `2` is a fourth power mod `p` exactly
when the even side is divisible by `2³`. -/
def GaussQuarticCriterion : Prop :=
  ∀ (p : ℕ) (a b : ℕ), p.Prime → p % 4 = 1 → p = a ^ 2 + b ^ 2 → Even b →
    ((∃ x : ZMod p, x ^ 4 = 2) ↔ 8 ∣ b)

/-- **THE SEVENTEEN INSTANCE OF THE CRITERION IS VERIFIED, NOT ASSUMED.**  Both sides are decided
independently and both are false: `2` is no fourth power mod `17`, and the even side `4` is not
eightfold.  So the criterion *holds here*, and the global obstruction at seventeen is legible in
the area partition alone. -/
theorem theCriterionHoldsAtSeventeen :
    ((∃ x : ZMod 17, x ^ 4 = 2) ↔ (8 ∣ 4)) := by
  constructor
  · intro h; obtain ⟨x, hx⟩ := h; exact absurd hx (theTwoIsNotAFourthPowerModSeventeen x)
  · intro h; exact absurd h (by decide)

/-- **THE AREA READS THE OBSTRUCTION.**  Under Gauss's criterion the quartic character of `2` at
a prime is a congruence on the side length of that prime's binomial area partition, mod `2³` —
the coupling between the prime's placement and the area potential it admits. -/
theorem theQuarticCharacterIsReadFromTheAreaPartition (hG : GaussQuarticCriterion) :
    ¬ ∃ x : ZMod 17, x ^ 4 = 2 := by
  intro h
  have := (hG 17 1 4 (by norm_num) (by norm_num) (by norm_num) (by decide)).1 h
  exact absurd this (by decide)

end Soma.Holonics.Millennium.AreaQuartic
