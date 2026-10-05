import Mathlib.Tactic

/-!
# The comma: a helix of fifths never closes on its octaves, and its remainders are exact

[proved-derived; formal-checked] October 5
([record](../../../research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md) §J3–J4).
Stack fifths `3 : 2` against octaves `2 : 1`. A stack of `m ≥ 1` fifths lands on a whole number of
octaves exactly when `3ᵐ = 2ᵏ`, which never happens: `3ᵐ` is odd and greater than one, `2ᵏ` is
one or even (`three_pow_ne_two_pow`). Factorization forbids the closure, so the helix of fifths
carries a remainder at every turn; its near-returns are the convergents of `log₂ 3`
(`Aeon/Clock/Lock`, the three-distance row of the atlas) and its remainders are the commas.

The remainders, carried exactly as ratios of factored integers:

```text
fourth = tone² · leimma        4 : 3 = (9 : 8)² · (2⁸ : 3⁵)            (timaeus_fourth)
apotome / leimma = comma       (3⁷ : 2¹¹) / (2⁸ : 3⁵) = 3¹² : 2¹⁹       (apotome_div_leimma)
comma                          (3 : 2)¹² / 2⁷ = 3¹² : 2¹⁹ = 531441 : 524288 (pythagorean_comma)
comma / syntonic = schisma     (3¹² : 2¹⁹) / (3⁴ : 2⁴·5) = 3⁸·5 : 2¹⁵   (comma_div_syntonic)
```

The leimma is the Timaeus's remainder (35b–36b): the World-Soul's fourths are filled with tones
and what is left is `256 : 243`. The comma is the difference of the two gap lengths of twelve
fifths, and the schisma is the remainder of one comma by another: the remainders compose their own
pattern of openings, recursively, as the Euclidean algorithm does on a remainder.
-/

namespace Holonics.Mathematics.Comma

/-- [proved-derived; formal-checked] **No stack of fifths closes on a whole number of octaves:**
`3ᵐ ≠ 2ᵏ` for every `m ≥ 1`. -/
theorem three_pow_ne_two_pow {m : ℕ} (hm : 0 < m) (k : ℕ) : 3 ^ m ≠ 2 ^ k := by
  intro h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : 1 < 3 ^ m := Nat.one_lt_pow hm.ne' (by norm_num)
    rw [h, pow_zero] at this
    exact lt_irrefl 1 this
  · have hodd : Odd (3 ^ m) := Odd.pow (by decide)
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk.ne'⟩
    rw [h] at hodd
    exact Nat.not_even_iff_odd.mpr hodd heven

/-- [proved-standard; formal-checked] **The Timaeus's fourth:** two tones and the leimma,
`4 : 3 = (9 : 8)² · (2⁸ : 3⁵)`. -/
theorem timaeus_fourth : ((9 : ℚ) / 8) ^ 2 * (2 ^ 8 / 3 ^ 5) = 4 / 3 := by norm_num

/-- [proved-standard; formal-checked] **The comma is the apotome less the leimma:**
`(3⁷ : 2¹¹) / (2⁸ : 3⁵) = 3¹² : 2¹⁹`. -/
theorem apotome_div_leimma :
    ((3 : ℚ) ^ 7 / 2 ^ 11) / (2 ^ 8 / 3 ^ 5) = 3 ^ 12 / 2 ^ 19 := by norm_num

/-- [proved-standard; formal-checked] **The Pythagorean comma:** twelve fifths over seven octaves,
`(3 : 2)¹² / 2⁷ = 3¹² : 2¹⁹ = 531441 : 524288`. -/
theorem pythagorean_comma :
    ((3 : ℚ) / 2) ^ 12 / 2 ^ 7 = 3 ^ 12 / 2 ^ 19 ∧ (3 : ℚ) ^ 12 / 2 ^ 19 = 531441 / 524288 := by
  constructor <;> norm_num

/-- [proved-standard; formal-checked] **A comma of commas:** the Pythagorean comma by the syntonic
`81 : 80 = 3⁴ : 2⁴·5` leaves the schisma `3⁸·5 : 2¹⁵ = 32805 : 32768`. -/
theorem comma_div_syntonic :
    ((3 : ℚ) ^ 12 / 2 ^ 19) / (3 ^ 4 / (2 ^ 4 * 5)) = 3 ^ 8 * 5 / 2 ^ 15 ∧
      (3 : ℚ) ^ 8 * 5 / 2 ^ 15 = 32805 / 32768 := by
  constructor <;> norm_num

end Holonics.Mathematics.Comma
