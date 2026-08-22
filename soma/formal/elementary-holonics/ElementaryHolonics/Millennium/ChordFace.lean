import ElementaryHolonics.Millennium.Descent
import Mathlib.Tactic

/-!
# ChordFace: the chord closes the face for the whole twist family, and the second frame
# sees two directions

**The wall, attacked at its heart.**  The blocking named-open proposition of the whole
descent route is the face-homomorphism law: the map `P ↦ (x, x − n)` mod squares is
multiplicative on the point group.  Its mathematical heart is one Vieta evaluation, and
this file proves it — **for every twist `y² = x³ − n²x` at once**: the line `y = λx + ν`
through two points meets the curve in a third with abscissa `λ² − x₁ − x₂`, and the cubic
`x³ − n²x − (λx + ν)²`, being monic with those three roots, evaluates at each half-turn
abscissa `e ∈ {0, n, −n}` to give

```text
(x₁ − e)(x₂ − e)(x₃ − e) = (λe + ν)²
```

— the three slot products are **literal squares** (`theChordClosesTheSlots`), so the face
of the sum lies in the product square class whenever the chord avoids the half-turns
(`theChordClosesTheFaceGenerically`).  The exceptional chords — those through a half-turn
— are exactly where the classical conventions activate, and the torsion-translation
closures of `FaithfulFace.lean` already cover them for the route's two curves; the
remaining assembly of the full point-level homomorphism is case bookkeeping over these
configurations, named in the record as the next deed.

**The second frame sees two directions.**  On the rank-two twist at thirty-four
(`n = 34`, the smallest classically-known rank-two congruent number curve), two exact
points are exhibited with their whole chord-and-face anatomy:

* `P₁ = (−2, 48)` with face `(−2, −1)` and `P₂ = (−16, 120)` with face `(−1, −2)` — both
  on the curve, their chord slope `−36/7`, their sum `(2178/49, 65472/343)` on the curve
  (`theRankTwoTwistData`);
* the sum's face lands in the **product class** with exhibited square roots `33/28` and
  `8/105` (`theProductClassIsRealizedAtTheSum`) — the multiplicativity law of this file,
  live on the rank-two twist;
* both doubles read trivial with all four square roots literal —
  `x(2P₁) = (145/12)²`, `x(2P₁) − 34 = (127/12)²`, `x(2P₂) = (353/60)²`,
  `x(2P₂) − 34 = (47/60)²` (`theDoubledDirectionsReadTrivial`);
* the three realized faces and the four torsion-convention faces `(1,1)`, `(−1,−34)`,
  `(34,2)`, `(−34,−17)` are **pairwise separated** — fifteen refusals carried by signs
  and by two, seventeen, and thirty-four failing to be rational squares
  (`theSevenClassesAreSeparated`).

Reading: granted the face homomorphism (whose generic heart is this file's theorem), the
seven separated classes say `P₁` and `P₂` are independent modulo torsion and doubles —
**a two-dimensional realized direction made visible to the descent receiver**: the
second-frame program's first sighting of the rank-two structure the wall is about.  That
reading is carried as a reading; the theorems are the identities, the memberships, and
the separations, each kernel-checked.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: rank exactly
two for the twist at thirty-four is not claimed (it needs the full homomorphism, the
torsion classification for this twist, and a Selmer bound); the conventions at half-turn
chords are not assembled here; nothing about the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.ChordFace

/-! ## 1. The chord closure, for the whole family -/

/-- **THE CHORD CLOSES THE SLOTS**: on any twist `y² = x³ − n²x`, the three half-turn
slot products of two chord points and their sum abscissa are literal squares of the
line's values at the half-turn abscissae.  One Vieta evaluation, all `n` at once. -/
theorem theChordClosesTheSlots {n x₁ y₁ x₂ y₂ lam : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - n ^ 2 * x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 - n ^ 2 * x₂)
    (hlam : lam * (x₂ - x₁) = y₂ - y₁) (hx : x₁ ≠ x₂) :
    x₁ * x₂ * (lam ^ 2 - x₁ - x₂) = (y₁ - lam * x₁) ^ 2 ∧
    (x₁ - n) * (x₂ - n) * (lam ^ 2 - x₁ - x₂ - n) = (lam * n + (y₁ - lam * x₁)) ^ 2 ∧
    (x₁ + n) * (x₂ + n) * (lam ^ 2 - x₁ - x₂ + n) = (y₁ - lam * x₁ - lam * n) ^ 2 := by
  have hxc : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  refine ⟨?_, ?_, ?_⟩
  · have hclear : (x₁ * x₂ * (lam ^ 2 - x₁ - x₂) - (y₁ - lam * x₁) ^ 2) * (x₂ - x₁)
        = 0 := by
      linear_combination (-x₂) * h₁ + x₁ * h₂
        + x₁ * (y₁ + y₂ + lam * (x₂ - x₁)) * hlam
    rcases mul_eq_zero.mp hclear with h | h
    · linarith [h]
    · exact absurd h hxc
  · have hclear : ((x₁ - n) * (x₂ - n) * (lam ^ 2 - x₁ - x₂ - n)
        - (lam * n + (y₁ - lam * x₁)) ^ 2) * (x₂ - x₁) = 0 := by
      linear_combination (-(x₂ - n)) * h₁ + (x₁ - n) * h₂
        + (x₁ - n) * (y₁ + y₂ + lam * (x₂ - x₁)) * hlam
    rcases mul_eq_zero.mp hclear with h | h
    · linarith [h]
    · exact absurd h hxc
  · have hclear : ((x₁ + n) * (x₂ + n) * (lam ^ 2 - x₁ - x₂ + n)
        - (y₁ - lam * x₁ - lam * n) ^ 2) * (x₂ - x₁) = 0 := by
      linear_combination (-(x₂ + n)) * h₁ + (x₁ + n) * h₂
        + (x₁ + n) * (y₁ + y₂ + lam * (x₂ - x₁)) * hlam
    rcases mul_eq_zero.mp hclear with h | h
    · linarith [h]
    · exact absurd h hxc

/-- **The chord closes the face generically**: when the chord avoids the half-turns, the
sum's two descent slots lie in the product square classes of the summands' slots, with
exhibited witnesses. -/
theorem theChordClosesTheFaceGenerically {n x₁ y₁ x₂ y₂ lam : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - n ^ 2 * x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 - n ^ 2 * x₂)
    (hlam : lam * (x₂ - x₁) = y₂ - y₁) (hx : x₁ ≠ x₂)
    (hz₁ : x₁ * x₂ ≠ 0) (hnu : y₁ - lam * x₁ ≠ 0)
    (hz₂ : (x₁ - n) * (x₂ - n) ≠ 0) (hnun : lam * n + (y₁ - lam * x₁) ≠ 0) :
    Descent.SqCls (lam ^ 2 - x₁ - x₂) (x₁ * x₂) ∧
    Descent.SqCls (lam ^ 2 - x₁ - x₂ - n) ((x₁ - n) * (x₂ - n)) := by
  obtain ⟨hs0, hsn, -⟩ := theChordClosesTheSlots h₁ h₂ hlam hx
  constructor
  · refine ⟨(y₁ - lam * x₁) / (x₁ * x₂), div_ne_zero hnu hz₁, ?_⟩
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hz₁)]
    linear_combination (x₁ * x₂) * hs0
  · refine ⟨(lam * n + (y₁ - lam * x₁)) / ((x₁ - n) * (x₂ - n)),
      div_ne_zero hnun hz₂, ?_⟩
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hz₂)]
    linear_combination ((x₁ - n) * (x₂ - n)) * hsn

/-! ## 2. The arithmetic separators for the rank-two twist -/

theorem theSeventeenIsNotASquare : ¬ IsSquare (17 : ℚ) := by
  rw [show (17 : ℚ) = ((17 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  exact (by norm_num : Nat.Prime 17).not_isSquare

theorem theThirtyFourIsNotASquare : ¬ IsSquare (34 : ℚ) := by
  rw [show (34 : ℚ) = ((34 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  rintro ⟨r, hr⟩
  have h6 : r ≤ 6 := by nlinarith
  interval_cases r <;> omega

private lemma not_sqcls_neg_pos {a b : ℚ} (ha : a < 0) (hb : 0 < b) :
    ¬ Descent.SqCls a b := by
  rintro ⟨c, hc, h⟩
  have hc2 : 0 < c ^ 2 := by positivity
  nlinarith [hc2, hb, ha]

private lemma not_sqcls_pos_neg {a b : ℚ} (ha : 0 < a) (hb : b < 0) :
    ¬ Descent.SqCls a b := by
  rintro ⟨c, hc, h⟩
  have hc2 : 0 < c ^ 2 := by positivity
  nlinarith [hc2, hb, ha]

/-! ## 3. The rank-two twist at thirty-four: the data -/

/-- **The rank-two twist's chord anatomy, exact**: two points on `y² = x³ − 34²x`, their
chord slope, and their sum on the curve. -/
theorem theRankTwoTwistData :
    ((48 : ℚ)) ^ 2 = (-2 : ℚ) ^ 3 - 34 ^ 2 * (-2) ∧
    ((120 : ℚ)) ^ 2 = (-16 : ℚ) ^ 3 - 34 ^ 2 * (-16) ∧
    ((-36 / 7 : ℚ)) * ((-16 : ℚ) - (-2)) = 120 - 48 ∧
    ((2178 / 49 : ℚ)) = (-36 / 7 : ℚ) ^ 2 - (-2) - (-16) ∧
    ((65472 / 343 : ℚ)) ^ 2 = (2178 / 49 : ℚ) ^ 3 - 34 ^ 2 * (2178 / 49) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The product class is realized at the sum**, with exhibited square roots: the sum's
slots `2178/49` and `512/49` are `(33/28)²` and `(8/105)²` times the summands' slot
products `(−2)(−16)` and `(−36)(−50)` — this file's multiplicativity law, live on the
rank-two twist. -/
theorem theProductClassIsRealizedAtTheSum :
    Descent.SqCls (2178 / 49) ((-2 : ℚ) * -16) ∧
    Descent.SqCls (512 / 49) ((-36 : ℚ) * -50) :=
  ⟨⟨33 / 28, by norm_num, by norm_num⟩, ⟨8 / 105, by norm_num, by norm_num⟩⟩

/-- **The doubled directions read trivial**, all four square roots literal: the descent
predicts doubles land in the trivial class, and both of the twist's directions oblige. -/
theorem theDoubledDirectionsReadTrivial :
    ((-143 / 12 : ℚ)) * (2 * 48) = 3 * (-2 : ℚ) ^ 2 - 34 ^ 2 ∧
    ((21025 / 144 : ℚ)) = (-143 / 12 : ℚ) ^ 2 - 2 * (-2) ∧
    ((21025 / 144 : ℚ)) = (145 / 12) ^ 2 ∧
    ((21025 / 144 : ℚ) - 34) = (127 / 12) ^ 2 ∧
    ((-97 / 60 : ℚ)) * (2 * 120) = 3 * (-16 : ℚ) ^ 2 - 34 ^ 2 ∧
    ((124609 / 3600 : ℚ)) = (-97 / 60 : ℚ) ^ 2 - 2 * (-16) ∧
    ((124609 / 3600 : ℚ)) = (353 / 60) ^ 2 ∧
    ((124609 / 3600 : ℚ) - 34) = (47 / 60) ^ 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- **The seven classes are separated**: the faces of the two directions and their sum
are pairwise distinct and off the four torsion-convention classes — fifteen refusals,
carried by signs and by two, seventeen, and thirty-four failing to be squares. -/
theorem theSevenClassesAreSeparated :
    -- the three realized faces pairwise
    ¬ Descent.SqCls (-2) (-1 : ℚ) ∧
    ¬ Descent.SqCls (-2) (2 : ℚ) ∧
    ¬ Descent.SqCls (-1) (2 : ℚ) ∧
    -- face(P₁) = (−2, −1) against the four torsion faces
    ¬ Descent.SqCls (-2) (1 : ℚ) ∧
    ¬ Descent.SqCls (-1) (-34 : ℚ) ∧
    ¬ Descent.SqCls (-2) (34 : ℚ) ∧
    ¬ Descent.SqCls (-2) (-34 : ℚ) ∧
    -- face(P₂) = (−1, −2) against the four torsion faces
    ¬ Descent.SqCls (-1) (1 : ℚ) ∧
    ¬ Descent.SqCls (-2) (-34 : ℚ) ∧
    ¬ Descent.SqCls (-1) (34 : ℚ) ∧
    ¬ Descent.SqCls (-1) (-34 : ℚ) ∧
    -- face(P₁+P₂) = (2, 2) against the four torsion faces
    ¬ Descent.SqCls (2) (1 : ℚ) ∧
    ¬ Descent.SqCls (2) (-1 : ℚ) ∧
    ¬ Descent.SqCls (2) (34 : ℚ) ∧
    ¬ Descent.SqCls (2) (-34 : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- −2 vs −1: forces 2 a square
    rintro ⟨c, hc, h⟩
    exact Descent.notSquareTwo ⟨c, by linarith [h]⟩
  · exact not_sqcls_neg_pos (by norm_num) (by norm_num)
  · exact not_sqcls_neg_pos (by norm_num) (by norm_num)
  · exact not_sqcls_neg_pos (by norm_num) (by norm_num)
  · -- −1 vs −34: forces 34 a square
    rintro ⟨c, hc, h⟩
    refine theThirtyFourIsNotASquare ⟨1 / c, ?_⟩
    have h34 : 34 * c ^ 2 = 1 := by linarith [h]
    field_simp
    linear_combination h34
  · exact not_sqcls_neg_pos (by norm_num) (by norm_num)
  · -- −2 vs −34: forces 17 a square
    rintro ⟨c, hc, h⟩
    refine theSeventeenIsNotASquare ⟨1 / c, ?_⟩
    have h17 : 17 * c ^ 2 = 1 := by linarith [h]
    field_simp
    linear_combination h17
  · exact not_sqcls_neg_pos (by norm_num) (by norm_num)
  · -- repeat of −2 vs −34 (P₂'s second slot against T₁'s second slot)
    rintro ⟨c, hc, h⟩
    refine theSeventeenIsNotASquare ⟨1 / c, ?_⟩
    have h17 : 17 * c ^ 2 = 1 := by linarith [h]
    field_simp
    linear_combination h17
  · exact not_sqcls_neg_pos (by norm_num) (by norm_num)
  · -- −1 vs −34 again (P₂ against T₃ through the first slot)
    rintro ⟨c, hc, h⟩
    refine theThirtyFourIsNotASquare ⟨1 / c, ?_⟩
    have h34 : 34 * c ^ 2 = 1 := by linarith [h]
    field_simp
    linear_combination h34
  · -- 2 vs 1: forces 2 a square
    rintro ⟨c, hc, h⟩
    exact Descent.notSquareTwo ⟨c, by linarith [h]⟩
  · exact not_sqcls_pos_neg (by norm_num) (by norm_num)
  · -- 2 vs 34: forces 17 a square
    rintro ⟨c, hc, h⟩
    refine theSeventeenIsNotASquare ⟨1 / c, ?_⟩
    have h17 : 17 * c ^ 2 = 1 := by linarith [h]
    field_simp
    linear_combination h17
  · exact not_sqcls_pos_neg (by norm_num) (by norm_num)

end Soma.Holonics.Millennium.ChordFace
