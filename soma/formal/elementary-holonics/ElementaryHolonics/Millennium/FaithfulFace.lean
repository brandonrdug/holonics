import ElementaryHolonics.Millennium.Descent
import ElementaryHolonics.Millennium.RankOne
import Mathlib.Tactic

/-!
# FaithfulFace: the descent face obeys its law on the families a two-descent actually uses

`Descent.lean` and `RankOne.lean` compute the descent face `P ↦ (x, x − 1)` — resp.
`(x, x − 5)` — on a *finite exhibited population* of points, and carry the homomorphism law as
the named-open `TheFaceIsAHomomorphismEverywhere`.  A law verified point by point is a table; the
receiver question of this wave is **the reading equals the population**, and a table cannot answer
it, because a table's agreement is forced at declaration.  This file replaces the table with
**general field identities in two free rational variables**: for *every* `(x, y)` on the curve with
`y ≠ 0`, the face closes over doubling and over translation by each half-turn.  Nothing here is a
per-point witness; every theorem quantifies over the whole curve.

One theorem is `rfl`-class and says so where it stands: `theTwoFilesDeclareOneSquareClass` is
`Iff.rfl`.  Everything else is a polynomial identity discharged modulo the curve equation, or a
nonvanishing argument resting on two not being a rational square.

## What is proved

Over `ℚ`, with `y ≠ 0` the only hypothesis beyond the curve equation:

* **The coordinate formulae are mathlib's own.**  `translatedX` and `doubledX` are proved equal to
  `WeierstrassCurve.Affine.addX` at mathlib's own `slope` — the secant case for a chord through a
  half-turn `(e, 0)`, the tangent case for doubling.  The identities below are therefore about the
  group law this repository already uses, not about a hand-rolled formula that resembles it.
* **Doubling reads trivial, generally.**  On `y² = x³ − x` the doubled abscissa satisfies
  `x₂·(4y²) = (x² + 1)²`, `(x₂ − 1)·(4y²) = (x² − 2x − 1)²` and `(x₂ + 1)·(4y²) = (x² + 2x − 1)²`;
  on `y² = x³ − 25x`, `(x² + 25)²`, `(x² − 10x − 25)²` and `(x² + 10x − 25)²`.  Dividing by the
  nonzero `4y²` exhibits both face slots of any doubled point as **literal rational squares**, with
  their square roots written out.  `RankOne.theDoubledSlotsAreSquares` observed this at the single
  point `2·(−4, 6) = (1681/144, −62279/1728)`, where `41/12` and `31/12` are exactly this file's
  `(x² + 25)/(2y)` and `(x² − 10x − 25)/(2y)` at `(−4, 6)`; here it is the whole curve.
* **A doubled point is never a half-turn.**  `x₂ ∉ {0, 1, −1}` resp. `x₂ ∉ {0, 5, −5}`, because
  `x₂ − 1 = 0` would make `x − 1` a rational square root of two.  So the trivial square class is
  reached with a *nonzero* representative, which is what the class needs, and the doubled slots lie
  in `Descent.SqCls · 1` and not merely in `IsSquare`.
* **Translation by each half-turn, as a field identity.**  `x(P + T₀) = −1/x`,
  `x(P + T₁) = (x + 1)/(x − 1)`, `x(P + T₋₁) = (1 − x)/(x + 1)` — note the third orientation; the
  numerator is `1 − x`, not `x − 1`, and the two differ by exactly the sign the face is sensitive
  to.  On the five-curve: `−25/x`, `5(x + 5)/(x − 5)`, `5(5 − x)/(x + 5)`.
* **A translated point is never a half-turn either**, so the face reads its slots as plain
  `(X, X − 1)` with no convention branch, on either curve.
* **The homomorphism closure, mod squares, on both slots of all three translations and both
  curves** — twelve identities, each of the form *claimed slot × predicted class product = an
  exhibited rational square*, the predicted class product taken against
  `Descent.slotOne Descent.P00` and its siblings, i.e. against the face values the earlier files
  computed, never against a constant re-declared here.  The exhibited squares are `1`, `y/x`,
  `y/(x − 1)`, `2`, `y/(x + 1)`, `2y/(x + 1)` and, on the five-curve, `25`, `5y/x`, `5y/(x − 5)`,
  `50`, `5y/(x + 5)`, `10y/(x + 5)`.  The square-class corollary is stated in the earlier files'
  own `SqCls`, which the two of them declare identically (`theTwoFilesDeclareOneSquareClass`).
* **The translation lifts to the point group.**  For a point of `Descent.E` and a half-turn with a
  different abscissa, the sum computed by mathlib's `Point.add` *is* the point at
  `translatedX x y e`, whose nonsingularity is supplied rather than assumed
  (`theTranslatedCoordinatesAreNonsingular`, `theTranslationIsTheGroupSum`).  So the half-turn
  coset of `Descent.TheFaceIsAHomomorphismEverywhere` is discharged at point level, not only in
  coordinates.  This was scoped as a named-open proposition and turned out to be six lines from
  `nonsingular_add` and `Point.add_of_X_ne`; carrying it open would have been a false absence.

## Classical provenance, cited and not reproved

The complete two-descent by the `x`-coordinate map into `(ℚ*/ℚ*²)²` for a curve with rational
two-torsion is Silverman 1986, *The Arithmetic of Elliptic Curves*, X.1.4 and X.4; the descent
method itself is Fermat 1640 for the congruent number one, and finite generation is Mordell 1922.
The conjecture these files sit under is Birch–Swinnerton-Dyer 1965.  None of that is proved here;
what is proved is the coordinate law, exactly.

**Measured 2026-08-21** over `Mathlib` at commit `a3a10db0`, toolchain `v4.27.0`:
`grep -rli "two.descent\|2.descent\|descent map" Mathlib --include='*.lean'` → 1 file,
`Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean`, unrelated; and
`grep -rl "IsSquare" Mathlib/AlgebraicGeometry/EllipticCurve --include='*.lean'` → 0 files.  Those
two commands measure those two name patterns over those two scopes; neither is a proof that no
related content exists under another name.

## Boundary — what this file does NOT claim

It does **not** prove the face is a homomorphism for every pair of points.  The families closed
here are doubling and translation by a half-turn — the coset structure a two-descent uses to reduce
`E(ℚ)/2E(ℚ)` to representatives — and the remaining coordinate obligation, the chord through two
points with distinct abscissae and neither of them a half-turn, is carried below as the named-open
`TheGeneralChordClosesTheFace` — stated on the five-curve, because on `y² = x³ − x` it would be
vacuous.  `Descent.TheFaceIsAHomomorphismEverywhere` and
`RankOne.TheFaceIsAHomomorphismEverywhere` stay open in their own files and are not weakened,
restated, or discharged here; only their half-turn coset is, and at point level only the first of
the two, since the five-curve gets no point-level lift.  **Doubling is lifted no further than
its coordinates**: `theTangentCoordinateIsMathlibsAddX` identifies the abscissa with mathlib's
`addX`, and the corresponding point-level statement is not proved, because the tangent case needs
`y ≠ negY x y` threaded through `add_self_of_Y_ne` and nothing below asks for it.

The face's **injectivity** is untouched: proving the law on these families says which classes are
hit, never that distinct classes stay distinct, and the kernel proposition
`Descent.TheKernelIsTheDoubledPopulation` is the converse of what is proved here — this file shows
doubles land in the trivial class, not that only doubles do.  No L-function, height pairing,
analytic rank, Selmer group or Tate–Shafarevich group appears, and no movement on
Birch–Swinnerton-Dyer is claimed by any theorem below.

Every theorem is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FaithfulFace

open Soma.Holonics.Millennium

/-! ## 1. The two coordinate formulae, and their identification with mathlib's `addX` -/

/-- The abscissa of `P + (e, 0)` for `P = (x, y)` on a curve with `a₁ = a₂ = a₃ = 0`: the chord
through the half-turn has slope `y/(x − e)`, and the third intersection sits at
`slope² − x − e`. -/
def translatedX (x y e : ℚ) : ℚ := (y / (x - e)) ^ 2 - x - e

/-- The abscissa of `2P` for `P = (x, y)` on `y² = x³ + a·x`: the tangent has slope
`(3x² + a)/(2y)`, and the doubled point sits at `slope² − 2x`. -/
def doubledX (x y a : ℚ) : ℚ := ((3 * x ^ 2 + a) / (2 * y)) ^ 2 - 2 * x

/-- **The chord formula is mathlib's `addX` at mathlib's `slope`.**  For a point `(x, y)` of
`Descent.E` and a half-turn `(e, 0)` with `x ≠ e`, the secant case of the group law returns
exactly `translatedX x y e`.  Everything proved about `translatedX` below is therefore proved
about the group law this repository already computes with. -/
theorem theChordCoordinateIsMathlibsAddX (x y e : ℚ) (hxe : x ≠ e) :
    Descent.E.addX x e (Descent.E.slope x e y 0) = translatedX x y e := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxe]
  simp only [WeierstrassCurve.Affine.addX, translatedX, Descent.E]
  ring

/-- **The tangent slope is the doubling slope.**  Mathlib's tangent case at `a₁ = a₂ = a₃ = 0` is
literally `(3x² + a₄)/(y − negY x y)`, and the denominator is `2y`. -/
theorem theTangentSlopeIsTheDoublingSlope (x y : ℚ) (hy : y ≠ 0) :
    Descent.E.slope x x y y = (3 * x ^ 2 + -1) / (2 * y) := by
  have hn : y ≠ Descent.E.negY x y := by
    simp only [WeierstrassCurve.Affine.negY, Descent.E]
    intro hc
    exact hy (by linarith)
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn]
  simp only [WeierstrassCurve.Affine.negY, Descent.E]
  congr 1 <;> ring

/-- **The doubling formula is mathlib's `addX` at the tangent slope**, on `Descent.E`. -/
theorem theTangentCoordinateIsMathlibsAddX (x y : ℚ) (hy : y ≠ 0) :
    Descent.E.addX x x (Descent.E.slope x x y y) = doubledX x y (-1) := by
  rw [theTangentSlopeIsTheDoublingSlope x y hy]
  simp only [WeierstrassCurve.Affine.addX, doubledX, Descent.E]
  ring

/-- **The doubling formula is mathlib's `addX` at the tangent slope**, on `RankOne.E5`. -/
theorem theTangentCoordinateIsMathlibsAddXOnTheFiveCurve (x y : ℚ) (hy : y ≠ 0) :
    RankOne.E5.addX x x (RankOne.E5.slope x x y y) = doubledX x y (-25) := by
  have hn : y ≠ RankOne.E5.negY x y := by
    simp only [WeierstrassCurve.Affine.negY, RankOne.E5]
    intro hc
    exact hy (by linarith)
  have hs : RankOne.E5.slope x x y y = (3 * x ^ 2 + -25) / (2 * y) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn]
    simp only [WeierstrassCurve.Affine.negY, RankOne.E5]
    congr 1 <;> ring
  rw [hs]
  simp only [WeierstrassCurve.Affine.addX, doubledX, RankOne.E5]
  ring

/-! ## 2. The square class, shared, and the two instruments -/

/-- **The two files declare one square class.**  *The proof is `Iff.rfl`* — `Descent.SqCls` and
`RankOne.SqCls` are the same relation on `ℚ`, so a closure proved against one is a closure against
the other, and this file states its corollaries once. -/
theorem theTwoFilesDeclareOneSquareClass (a b : ℚ) : Descent.SqCls a b ↔ RankOne.SqCls a b :=
  Iff.rfl

/-- A product identity is a square-class membership: if `a·b` is a nonzero square and `b ≠ 0`,
then `a` and `b` share a square class, with the witness `s/b`. -/
private lemma sqClsOfProductSquare {a b s : ℚ} (hb : b ≠ 0) (hs : s ≠ 0) (h : a * b = s ^ 2) :
    Descent.SqCls a b := by
  refine ⟨s / b, div_ne_zero hs hb, ?_⟩
  field_simp
  linear_combination h

/-- Two is not a rational square, so no rational `u, c` with `c ≠ 0` satisfy `u² = 2c²`.  This is
the one arithmetic fact that keeps a doubled point off the half-turns; it is
`Descent.notSquareTwo` applied to `u/c`. -/
private lemma noRationalRootOfTwo {u c : ℚ} (hc : c ≠ 0) (h : u ^ 2 = 2 * c ^ 2) : False := by
  refine Descent.notSquareTwo ⟨u / c, ?_⟩
  field_simp
  linear_combination -h

/-- **The doubling numerators never vanish**, on either curve.  Two of the six are positive by
inspection; the other four would each make two a rational square — `(x − 1)² = 2`,
`(x + 1)² = 2`, `((x − 5)/5)² = 2`, `((x + 5)/5)² = 2`.  This single arithmetic fact is what keeps
a doubled point off the half-turns, and it is the same fact `Descent.notSquareTwo` uses to
separate the four torsion classes: the arithmetic paying twice for one geometry. -/
theorem theDoublingNumeratorsNeverVanish (x : ℚ) :
    x ^ 2 + 1 ≠ 0 ∧ x ^ 2 - 2 * x - 1 ≠ 0 ∧ x ^ 2 + 2 * x - 1 ≠ 0 ∧
    x ^ 2 + 25 ≠ 0 ∧ x ^ 2 - 10 * x - 25 ≠ 0 ∧ x ^ 2 + 10 * x - 25 ≠ 0 := by
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · nlinarith [sq_nonneg x]
  · exact noRationalRootOfTwo (u := x - 1) (c := 1) one_ne_zero (by linear_combination h0)
  · exact noRationalRootOfTwo (u := x + 1) (c := 1) one_ne_zero (by linear_combination h0)
  · nlinarith [sq_nonneg x]
  · exact noRationalRootOfTwo (u := x - 5) (c := 5) (by norm_num) (by linear_combination h0)
  · exact noRationalRootOfTwo (u := x + 5) (c := 5) (by norm_num) (by linear_combination h0)

/-- **A nonzero ordinate avoids all three roots.**  On `y² = x³ − x`, `y ≠ 0` forces
`x ∉ {0, 1, −1}` — the affine point is not a half-turn, and every denominator below is
nonzero. -/
theorem theNonzeroOrdinateAvoidsTheThreeRoots {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact hy (sq_eq_zero_iff.mp (by rw [h]; norm_num))

/-- **A nonzero ordinate avoids all three roots**, on `y² = x³ − 25x`. -/
theorem theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve {x y : ℚ}
    (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) : x ≠ 0 ∧ x ≠ 5 ∧ x ≠ -5 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact hy (sq_eq_zero_iff.mp (by rw [h]; norm_num))

/-! ## 3. Doubling reads trivial on `y² = x³ − x`, generally

The three identities are stated over the common denominator `4y²`, which is where they are
polynomial; the square roots are extracted immediately afterwards. -/

/-- **The doubled first slot, over the ordinate**: `x₂·(4y²) = (x² + 1)²`. -/
theorem theDoubledFirstSlotIsASquareOverFourYSquared {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) : doubledX x y (-1) * (4 * y ^ 2) = (x ^ 2 + 1) ^ 2 := by
  have key : doubledX x y (-1) * (4 * y ^ 2) = (3 * x ^ 2 - 1) ^ 2 - 8 * x * y ^ 2 := by
    simp only [doubledX]
    field_simp
    ring
  rw [key, h]; ring

/-- **The doubled second slot, over the ordinate**: `(x₂ − 1)·(4y²) = (x² − 2x − 1)²`. -/
theorem theDoubledSecondSlotIsASquareOverFourYSquared {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) : (doubledX x y (-1) - 1) * (4 * y ^ 2) = (x ^ 2 - 2 * x - 1) ^ 2 := by
  have hsplit : (doubledX x y (-1) - 1) * (4 * y ^ 2)
      = doubledX x y (-1) * (4 * y ^ 2) - 4 * y ^ 2 := by ring
  rw [hsplit, theDoubledFirstSlotIsASquareOverFourYSquared h hy, h]; ring

/-- **The doubled third slot, over the ordinate**: `(x₂ + 1)·(4y²) = (x² + 2x − 1)²`.  The third
root's slot is not part of the face — the face has two slots — but it is what the third half-turn
would read, and the descent's product relation `x·(x − 1)·(x + 1) = y²` needs it. -/
theorem theDoubledThirdSlotIsASquareOverFourYSquared {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) : (doubledX x y (-1) + 1) * (4 * y ^ 2) = (x ^ 2 + 2 * x - 1) ^ 2 := by
  have hsplit : (doubledX x y (-1) + 1) * (4 * y ^ 2)
      = doubledX x y (-1) * (4 * y ^ 2) + 4 * y ^ 2 := by ring
  rw [hsplit, theDoubledFirstSlotIsASquareOverFourYSquared h hy, h]; ring

/-- **A doubled point is never a half-turn.**  `x₂ = 1` would give `(x − 1)² = 2` and `x₂ = −1`
would give `(x + 1)² = 2`; `x₂ = 0` would give `x² + 1 = 0`.  So `2·P` never lands on the torsion
the face reads by convention, and its slots are read as plain `(x₂, x₂ − 1)`. -/
theorem theDoubledPointIsNeverAHalfTurn {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    doubledX x y (-1) ≠ 0 ∧ doubledX x y (-1) ≠ 1 ∧ doubledX x y (-1) ≠ -1 := by
  obtain ⟨n1, n2, n3, -, -, -⟩ := theDoublingNumeratorsNeverVanish x
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · have := theDoubledFirstSlotIsASquareOverFourYSquared h hy
    rw [hc] at this
    exact n1 (sq_eq_zero_iff.mp (by linarith [this]))
  · have := theDoubledSecondSlotIsASquareOverFourYSquared h hy
    rw [hc] at this
    exact n2 (sq_eq_zero_iff.mp (by linarith [this]))
  · have := theDoubledThirdSlotIsASquareOverFourYSquared h hy
    rw [hc] at this
    exact n3 (sq_eq_zero_iff.mp (by linarith [this]))

/-- **Both face slots of a doubled point are literal rational squares**, with their roots
exhibited: `x₂ = ((x² + 1)/(2y))²` and `x₂ − 1 = ((x² − 2x − 1)/(2y))²`.  This is the descent's
"the kernel contains the doubles", as a field identity on the whole curve rather than as an
observation at one point. -/
theorem theDoubledSlotsAreSquares {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    doubledX x y (-1) = ((x ^ 2 + 1) / (2 * y)) ^ 2 ∧
    doubledX x y (-1) - 1 = ((x ^ 2 - 2 * x - 1) / (2 * y)) ^ 2 := by
  have h4 : (4 : ℚ) * y ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
  constructor
  · refine mul_right_cancel₀ h4 ?_
    rw [theDoubledFirstSlotIsASquareOverFourYSquared h hy]
    field_simp
    ring
  · refine mul_right_cancel₀ h4 ?_
    rw [theDoubledSecondSlotIsASquareOverFourYSquared h hy]
    field_simp
    ring

/-- **The doubled point lands in the trivial square class, on both slots.**  Stated in
`Descent.SqCls`, the relation `Descent.lean` uses for its own face computations: `SqCls a 1` says
`a` is a *nonzero* square, and the nonzero half is exactly
`theDoubledPointIsNeverAHalfTurn`. -/
theorem theDoubledSlotsAreTheTrivialClass {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    Descent.SqCls (doubledX x y (-1)) 1 ∧ Descent.SqCls (doubledX x y (-1) - 1) 1 := by
  obtain ⟨n1, n2, -, -, -, -⟩ := theDoublingNumeratorsNeverVanish x
  obtain ⟨hsq1, hsq2⟩ := theDoubledSlotsAreSquares h hy
  have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero two_ne_zero hy
  constructor
  · exact sqClsOfProductSquare one_ne_zero (s := (x ^ 2 + 1) / (2 * y))
      (div_ne_zero n1 h2y) (by rw [mul_one]; exact hsq1)
  · exact sqClsOfProductSquare one_ne_zero (s := (x ^ 2 - 2 * x - 1) / (2 * y))
      (div_ne_zero n2 h2y) (by rw [mul_one]; exact hsq2)

/-! ## 4. Translation by each half-turn, on `y² = x³ − x` -/

/-- **Translation by the half-turn at zero**: `x(P + (0,0)) = −1/x`.  The chord through the
origin; the identity is `y²/x² − x = −1/x` given the curve equation. -/
theorem theHalfTurnAtZeroTranslates {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    translatedX x y 0 = -1 / x := by
  obtain ⟨hx0, -, -⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  have e0 : translatedX x y 0 = (y / x) ^ 2 - x := by simp [translatedX]
  rw [e0, div_pow, h]
  field_simp
  ring

/-- **Translation by the half-turn at one**: `x(P + (1,0)) = (x + 1)/(x − 1)`. -/
theorem theHalfTurnAtOneTranslates {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    translatedX x y 1 = (x + 1) / (x - 1) := by
  obtain ⟨-, hx1, -⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [translatedX, div_pow]
  rw [h]
  field_simp
  ring

/-- **Translation by the half-turn at minus one**: `x(P + (−1,0)) = (1 − x)/(x + 1)`.  The
numerator is `1 − x`; the orientation is load-bearing, because `(x − 1)/(x + 1)` differs from it
by `−1`, and `−1` is precisely the class `Descent.lean` proves is not the trivial class. -/
theorem theHalfTurnAtNegativeOneTranslates {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    translatedX x y (-1) = (1 - x) / (x + 1) := by
  obtain ⟨-, -, hxm1⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  have hd : x + 1 ≠ 0 := fun hc => hxm1 (by linarith)
  have e0 : translatedX x y (-1) = (y / (x + 1)) ^ 2 - x + 1 := by
    simp only [translatedX]; ring_nf
  rw [e0, div_pow, h]
  field_simp
  ring

/-- **A translated point is never a half-turn.**  Each of `−1/x`, `(x + 1)/(x − 1)` and
`(1 − x)/(x + 1)` misses `{0, 1, −1}` for every admissible `x`, so the translated point's face
slots are read as plain `(X, X − 1)` and no convention branch fires.  Without this the closure
identities below would be about a value the face does not use. -/
theorem theTranslatedPointIsNeverAHalfTurn {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    (translatedX x y 0 ≠ 0 ∧ translatedX x y 0 ≠ 1 ∧ translatedX x y 0 ≠ -1) ∧
    (translatedX x y 1 ≠ 0 ∧ translatedX x y 1 ≠ 1 ∧ translatedX x y 1 ≠ -1) ∧
    (translatedX x y (-1) ≠ 0 ∧ translatedX x y (-1) ≠ 1 ∧ translatedX x y (-1) ≠ -1) := by
  obtain ⟨hx0, hx1, hxm1⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  have hd1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hd2 : x + 1 ≠ 0 := fun hc => hxm1 (by linarith)
  rw [theHalfTurnAtZeroTranslates h hy, theHalfTurnAtOneTranslates h hy,
    theHalfTurnAtNegativeOneTranslates h hy]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro hc; rw [div_eq_iff hx0] at hc; linarith
  · intro hc; rw [div_eq_iff hx0] at hc; exact hxm1 (by linarith)
  · intro hc; rw [div_eq_iff hx0] at hc; exact hx1 (by linarith)
  · intro hc; rw [div_eq_iff hd1] at hc; exact hxm1 (by linarith)
  · intro hc; rw [div_eq_iff hd1] at hc; linarith
  · intro hc; rw [div_eq_iff hd1] at hc; exact hx0 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc; exact hx1 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc; exact hx0 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc; linarith

/-! ## 5. The homomorphism closure on `y² = x³ − x`

Each identity reads *claimed slot × predicted class product = an exhibited rational square*.  The
predicted class product is taken against `Descent.slotOne`/`Descent.slotTwo` evaluated at the
half-turn points of `Descent.lean` — the face values that file computed, not constants
re-declared here. -/

/-- **The half-turn at zero closes both slots**: `(−1/x)·(x·(−1)) = 1²` and
`(−1/x − 1)·((x − 1)·(−1)) = (y/x)²`.  The second is where the curve equation enters: the product
is `(x² − 1)/x`, which is `y²/x²` exactly because `y² = x(x² − 1)`. -/
theorem theHalfTurnAtZeroClosesBothSlots {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    translatedX x y 0 * (x * Descent.slotOne Descent.P00) = (1 : ℚ) ^ 2 ∧
    (translatedX x y 0 - 1) * ((x - 1) * Descent.slotTwo Descent.P00) = (y / x) ^ 2 := by
  obtain ⟨-, ⟨a1, a2⟩, -, -⟩ := Descent.theFourFaceValues
  obtain ⟨hx0, -, -⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  rw [a1, a2, theHalfTurnAtZeroTranslates h hy]
  simp only [div_pow]
  rw [h]
  constructor <;> (field_simp; try ring)

/-- **The half-turn at one closes both slots**: `((x+1)/(x−1))·(x·1) = (y/(x−1))²` and
`((x+1)/(x−1) − 1)·((x − 1)·2) = 2²`.  The first is the curve equation again — `x(x + 1)` is
`y²/(x − 1)` — and the second is a clean cancellation. -/
theorem theHalfTurnAtOneClosesBothSlots {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    translatedX x y 1 * (x * Descent.slotOne Descent.P10) = (y / (x - 1)) ^ 2 ∧
    (translatedX x y 1 - 1) * ((x - 1) * Descent.slotTwo Descent.P10) = (2 : ℚ) ^ 2 := by
  obtain ⟨-, -, ⟨b1, b2⟩, -⟩ := Descent.theFourFaceValues
  obtain ⟨-, hx1, -⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  rw [b1, b2, theHalfTurnAtOneTranslates h hy]
  simp only [div_pow]
  rw [h]
  constructor <;> (field_simp; try ring)

/-- **The half-turn at minus one closes both slots**: `((1−x)/(x+1))·(x·(−1)) = (y/(x+1))²` and
`((1−x)/(x+1) − 1)·((x − 1)·(−2)) = (2y/(x+1))²`.  Both need the `1 − x` orientation; with
`(x − 1)/(x + 1)` the first product is `−y²/(x+1)²`, which is not a square. -/
theorem theHalfTurnAtNegativeOneClosesBothSlots {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    translatedX x y (-1) * (x * Descent.slotOne Descent.Pm10) = (y / (x + 1)) ^ 2 ∧
    (translatedX x y (-1) - 1) * ((x - 1) * Descent.slotTwo Descent.Pm10)
      = (2 * y / (x + 1)) ^ 2 := by
  obtain ⟨-, -, -, ⟨c1, c2⟩⟩ := Descent.theFourFaceValues
  obtain ⟨-, -, hxm1⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  have hd : x + 1 ≠ 0 := fun hc => hxm1 (by linarith)
  rw [c1, c2, theHalfTurnAtNegativeOneTranslates h hy]
  simp only [div_pow, mul_pow]
  rw [h]
  constructor <;> (field_simp; try ring)

/-- **The face law closes on every half-turn translation**, in `Descent.SqCls` — the six
memberships the three closure theorems above supply, gathered as the statement a two-descent
uses.  For every point of `y² = x³ − x` off the two-torsion and for each of the three half-turns,
both slots of the translated point lie in the square class of the product of slots.  This is
`Descent.TheFaceIsAHomomorphismEverywhere` restricted to `Q` a half-turn, proved. -/
theorem theFaceLawClosesOnEveryHalfTurnTranslation {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    Descent.SqCls (translatedX x y 0) (x * Descent.slotOne Descent.P00) ∧
    Descent.SqCls (translatedX x y 0 - 1) ((x - 1) * Descent.slotTwo Descent.P00) ∧
    Descent.SqCls (translatedX x y 1) (x * Descent.slotOne Descent.P10) ∧
    Descent.SqCls (translatedX x y 1 - 1) ((x - 1) * Descent.slotTwo Descent.P10) ∧
    Descent.SqCls (translatedX x y (-1)) (x * Descent.slotOne Descent.Pm10) ∧
    Descent.SqCls (translatedX x y (-1) - 1) ((x - 1) * Descent.slotTwo Descent.Pm10) := by
  obtain ⟨-, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := Descent.theFourFaceValues
  obtain ⟨hx0, hx1, hxm1⟩ := theNonzeroOrdinateAvoidsTheThreeRoots h hy
  have hd1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hd2 : x + 1 ≠ 0 := fun hc => hxm1 (by linarith)
  obtain ⟨z1, z2⟩ := theHalfTurnAtZeroClosesBothSlots h hy
  obtain ⟨o1, o2⟩ := theHalfTurnAtOneClosesBothSlots h hy
  obtain ⟨m1, m2⟩ := theHalfTurnAtNegativeOneClosesBothSlots h hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sqClsOfProductSquare (by rw [a1]; exact mul_ne_zero hx0 (by norm_num)) one_ne_zero z1
  · exact sqClsOfProductSquare (by rw [a2]; exact mul_ne_zero hd1 (by norm_num))
      (div_ne_zero hy hx0) z2
  · exact sqClsOfProductSquare (by rw [b1]; exact mul_ne_zero hx0 (by norm_num))
      (div_ne_zero hy hd1) o1
  · exact sqClsOfProductSquare (by rw [b2]; exact mul_ne_zero hd1 (by norm_num)) two_ne_zero o2
  · exact sqClsOfProductSquare (by rw [c1]; exact mul_ne_zero hx0 (by norm_num))
      (div_ne_zero hy hd2) m1
  · exact sqClsOfProductSquare (by rw [c2]; exact mul_ne_zero hd1 (by norm_num))
      (div_ne_zero (mul_ne_zero two_ne_zero hy) hd2) m2

/-! ## 6. The same two families on `y² = x³ − 25x`

`RankOne.lean`'s curve, slots `(x, x − 5)`.  The doubling triple and the three translations carry
the same shape with the root population `{0, 5, −5}`; the exhibited squares pick up the factors
of five the wider root spacing supplies. -/

/-- **The doubled first slot, over the ordinate**: `x₂·(4y²) = (x² + 25)²`. -/
theorem theDoubledFirstSlotOnTheFiveCurve {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    doubledX x y (-25) * (4 * y ^ 2) = (x ^ 2 + 25) ^ 2 := by
  have key : doubledX x y (-25) * (4 * y ^ 2) = (3 * x ^ 2 - 25) ^ 2 - 8 * x * y ^ 2 := by
    simp only [doubledX]
    field_simp
    ring
  rw [key, h]; ring

/-- **The doubled second slot, over the ordinate**: `(x₂ − 5)·(4y²) = (x² − 10x − 25)²`. -/
theorem theDoubledSecondSlotOnTheFiveCurve {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    (doubledX x y (-25) - 5) * (4 * y ^ 2) = (x ^ 2 - 10 * x - 25) ^ 2 := by
  have hsplit : (doubledX x y (-25) - 5) * (4 * y ^ 2)
      = doubledX x y (-25) * (4 * y ^ 2) - 20 * y ^ 2 := by ring
  rw [hsplit, theDoubledFirstSlotOnTheFiveCurve h hy, h]; ring

/-- **The doubled third slot, over the ordinate**: `(x₂ + 5)·(4y²) = (x² + 10x − 25)²`. -/
theorem theDoubledThirdSlotOnTheFiveCurve {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    (doubledX x y (-25) + 5) * (4 * y ^ 2) = (x ^ 2 + 10 * x - 25) ^ 2 := by
  have hsplit : (doubledX x y (-25) + 5) * (4 * y ^ 2)
      = doubledX x y (-25) * (4 * y ^ 2) + 20 * y ^ 2 := by ring
  rw [hsplit, theDoubledFirstSlotOnTheFiveCurve h hy, h]; ring

/-- **A doubled point is never a half-turn**, on the five-curve: `x₂ = 5` would give
`((x − 5)/5)² = 2`, and `x₂ = −5` would give `((x + 5)/5)² = 2`. -/
theorem theDoubledPointIsNeverAHalfTurnOnTheFiveCurve {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x)
    (hy : y ≠ 0) :
    doubledX x y (-25) ≠ 0 ∧ doubledX x y (-25) ≠ 5 ∧ doubledX x y (-25) ≠ -5 := by
  obtain ⟨-, -, -, n4, n5, n6⟩ := theDoublingNumeratorsNeverVanish x
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · have := theDoubledFirstSlotOnTheFiveCurve h hy
    rw [hc] at this
    exact n4 (sq_eq_zero_iff.mp (by linarith [this]))
  · have := theDoubledSecondSlotOnTheFiveCurve h hy
    rw [hc] at this
    exact n5 (sq_eq_zero_iff.mp (by linarith [this]))
  · have := theDoubledThirdSlotOnTheFiveCurve h hy
    rw [hc] at this
    exact n6 (sq_eq_zero_iff.mp (by linarith [this]))

/-- **Both face slots of a doubled point are literal rational squares**, on the five-curve, with
roots `(x² + 25)/(2y)` and `(x² − 10x − 25)/(2y)`.  At `(x, y) = (−4, 6)` these are `41/12` and
`31/12`, which are exactly the roots `RankOne.theDoubledSlotsAreSquares` exhibits at that one
point; here the identity holds on the whole curve. -/
theorem theDoubledSlotsAreSquaresOnTheFiveCurve {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x)
    (hy : y ≠ 0) :
    doubledX x y (-25) = ((x ^ 2 + 25) / (2 * y)) ^ 2 ∧
    doubledX x y (-25) - 5 = ((x ^ 2 - 10 * x - 25) / (2 * y)) ^ 2 := by
  have h4 : (4 : ℚ) * y ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
  constructor
  · refine mul_right_cancel₀ h4 ?_
    rw [theDoubledFirstSlotOnTheFiveCurve h hy]
    field_simp
    ring
  · refine mul_right_cancel₀ h4 ?_
    rw [theDoubledSecondSlotOnTheFiveCurve h hy]
    field_simp
    ring

/-- **Translation by the half-turn at zero**, five-curve: `x(P + (0,0)) = −25/x`. -/
theorem theHalfTurnAtZeroTranslatesOnTheFiveCurve {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x)
    (hy : y ≠ 0) : translatedX x y 0 = -25 / x := by
  obtain ⟨hx0, -, -⟩ := theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  have e0 : translatedX x y 0 = (y / x) ^ 2 - x := by simp [translatedX]
  rw [e0, div_pow, h]
  field_simp
  ring

/-- **Translation by the half-turn at five**: `x(P + (5,0)) = 5(x + 5)/(x − 5)`. -/
theorem theHalfTurnAtFiveTranslates {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    translatedX x y 5 = 5 * (x + 5) / (x - 5) := by
  obtain ⟨-, hx5, -⟩ := theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  have hd : x - 5 ≠ 0 := sub_ne_zero.mpr hx5
  simp only [translatedX, div_pow]
  rw [h]
  field_simp
  ring

/-- **Translation by the half-turn at minus five**: `x(P + (−5,0)) = 5(5 − x)/(x + 5)` — the same
`5 − x` orientation the one-curve carries at its own negative root. -/
theorem theHalfTurnAtNegativeFiveTranslates {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    translatedX x y (-5) = 5 * (5 - x) / (x + 5) := by
  obtain ⟨-, -, hxm5⟩ := theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  have hd : x + 5 ≠ 0 := fun hc => hxm5 (by linarith)
  have e0 : translatedX x y (-5) = (y / (x + 5)) ^ 2 - x + 5 := by
    simp only [translatedX]; ring_nf
  rw [e0, div_pow, h]
  field_simp
  ring

/-- **The half-turn at zero closes both slots**, five-curve: `(−25/x)·(x·(−25)) = 25²` and
`(−25/x − 5)·((x − 5)·(−5)) = (5y/x)²`. -/
theorem theHalfTurnAtZeroClosesBothSlotsOnTheFiveCurve {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x)
    (hy : y ≠ 0) :
    translatedX x y 0 * (x * RankOne.slotOne RankOne.T0) = (25 : ℚ) ^ 2 ∧
    (translatedX x y 0 - 5) * ((x - 5) * RankOne.slotTwo RankOne.T0) = (5 * y / x) ^ 2 := by
  obtain ⟨-, ⟨a1, a2⟩, -, -, -, -⟩ := RankOne.theFaceValues
  obtain ⟨hx0, -, -⟩ := theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  rw [a1, a2, theHalfTurnAtZeroTranslatesOnTheFiveCurve h hy]
  simp only [div_pow, mul_pow]
  rw [h]
  constructor <;> (field_simp; try ring)

/-- **The half-turn at five closes both slots**: `(5(x+5)/(x−5))·(x·5) = (5y/(x−5))²` and
`(5(x+5)/(x−5) − 5)·((x − 5)·50) = 50²`. -/
theorem theHalfTurnAtFiveClosesBothSlots {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    translatedX x y 5 * (x * RankOne.slotOne RankOne.T5) = (5 * y / (x - 5)) ^ 2 ∧
    (translatedX x y 5 - 5) * ((x - 5) * RankOne.slotTwo RankOne.T5) = (50 : ℚ) ^ 2 := by
  obtain ⟨-, -, ⟨b1, b2⟩, -, -, -⟩ := RankOne.theFaceValues
  obtain ⟨-, hx5, -⟩ := theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  have hd : x - 5 ≠ 0 := sub_ne_zero.mpr hx5
  rw [b1, b2, theHalfTurnAtFiveTranslates h hy]
  simp only [div_pow, mul_pow]
  rw [h]
  constructor <;> (field_simp; try ring)

/-- **The half-turn at minus five closes both slots**:
`(5(5−x)/(x+5))·(x·(−5)) = (5y/(x+5))²` and
`(5(5−x)/(x+5) − 5)·((x − 5)·(−10)) = (10y/(x+5))²`. -/
theorem theHalfTurnAtNegativeFiveClosesBothSlots {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x)
    (hy : y ≠ 0) :
    translatedX x y (-5) * (x * RankOne.slotOne RankOne.Tm5) = (5 * y / (x + 5)) ^ 2 ∧
    (translatedX x y (-5) - 5) * ((x - 5) * RankOne.slotTwo RankOne.Tm5)
      = (10 * y / (x + 5)) ^ 2 := by
  obtain ⟨-, -, -, ⟨c1, c2⟩, -, -⟩ := RankOne.theFaceValues
  obtain ⟨-, -, hxm5⟩ := theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  have hd : x + 5 ≠ 0 := fun hc => hxm5 (by linarith)
  rw [c1, c2, theHalfTurnAtNegativeFiveTranslates h hy]
  simp only [div_pow, mul_pow]
  rw [h]
  constructor <;> (field_simp; try ring)

/-- **The face law closes on every half-turn translation**, five-curve, in `RankOne.SqCls`.  With
`RankOne.theDoubledSlotsAreSquares`'s single-point observation now general
(`theDoubledSlotsAreSquaresOnTheFiveCurve`), the descent's coset structure on this rank-one curve
is established: the classes of `P`, `P + T₀`, `P + T₅`, `P + T₋₅` are the four translates of one
class, and doubling returns to the trivial one. -/
theorem theFaceLawClosesOnEveryHalfTurnTranslationOnTheFiveCurve {x y : ℚ}
    (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    RankOne.SqCls (translatedX x y 0) (x * RankOne.slotOne RankOne.T0) ∧
    RankOne.SqCls (translatedX x y 0 - 5) ((x - 5) * RankOne.slotTwo RankOne.T0) ∧
    RankOne.SqCls (translatedX x y 5) (x * RankOne.slotOne RankOne.T5) ∧
    RankOne.SqCls (translatedX x y 5 - 5) ((x - 5) * RankOne.slotTwo RankOne.T5) ∧
    RankOne.SqCls (translatedX x y (-5)) (x * RankOne.slotOne RankOne.Tm5) ∧
    RankOne.SqCls (translatedX x y (-5) - 5) ((x - 5) * RankOne.slotTwo RankOne.Tm5) := by
  obtain ⟨-, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, -, -⟩ := RankOne.theFaceValues
  obtain ⟨hx0, hx5, hxm5⟩ := theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  have hd1 : x - 5 ≠ 0 := sub_ne_zero.mpr hx5
  have hd2 : x + 5 ≠ 0 := fun hc => hxm5 (by linarith)
  obtain ⟨z1, z2⟩ := theHalfTurnAtZeroClosesBothSlotsOnTheFiveCurve h hy
  obtain ⟨o1, o2⟩ := theHalfTurnAtFiveClosesBothSlots h hy
  obtain ⟨m1, m2⟩ := theHalfTurnAtNegativeFiveClosesBothSlots h hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sqClsOfProductSquare (by rw [a1]; exact mul_ne_zero hx0 (by norm_num)) (by norm_num) z1
  · exact sqClsOfProductSquare (by rw [a2]; exact mul_ne_zero hd1 (by norm_num))
      (div_ne_zero (mul_ne_zero (by norm_num) hy) hx0) z2
  · exact sqClsOfProductSquare (by rw [b1]; exact mul_ne_zero hx0 (by norm_num))
      (div_ne_zero (mul_ne_zero (by norm_num) hy) hd1) o1
  · exact sqClsOfProductSquare (by rw [b2]; exact mul_ne_zero hd1 (by norm_num)) (by norm_num) o2
  · exact sqClsOfProductSquare (by rw [c1]; exact mul_ne_zero hx0 (by norm_num))
      (div_ne_zero (mul_ne_zero (by norm_num) hy) hd2) m1
  · exact sqClsOfProductSquare (by rw [c2]; exact mul_ne_zero hd1 (by norm_num))
      (div_ne_zero (mul_ne_zero (by norm_num) hy) hd2) m2

/-! ## 7. The one family left open, named -/

/-- The abscissa of `P + Q` for two points with distinct abscissae: the secant's slope squared,
less the two abscissae. -/
def chordX (x₁ y₁ x₂ y₂ : ℚ) : ℚ := ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - x₁ - x₂

/-- **The general chord closes the face**, on the rank-one curve `y² = x³ − 25x`.  For two points
with distinct abscissae, neither a half-turn, and whose chord does not land on a half-turn either,
both face slots of the third intersection lie in the square class of the product of slots — the
same law this file proves for doubling and for translation by a half-turn, on the one family it
does not reach.

**It is stated on the five-curve deliberately.**  The identical statement over `y² = x³ − x` is
classically *vacuous*: that curve has no rational point with `y ≠ 0`, so the hypotheses are never
satisfiable and the proposition would be `True` wearing a quantifier.  The five-curve has rank one,
so its hypotheses are satisfied by infinitely many pairs and the proposition has content.

**The last two hypotheses are not decoration.**  If the chord lands on `(0,0)` the first slot is
`0`, and `SqCls 0 b` is false — the face's convention at a vanishing coordinate is what handles
that case, and it lives on `WeierstrassCurve.Affine.Point`, not on these coordinates.

*Aside: this is the remaining coordinate obligation behind
`RankOne.TheFaceIsAHomomorphismEverywhere` and its sibling on the one-curve, and it is classically
true (Silverman 1986, X.1.4).  Checked here in exactly this guarded form, in exact rational
arithmetic, over 15 points with `y ≠ 0` drawn from `{kP : 1 ≤ k ≤ 8} ∪ {T + P, T + 2P, −P}` with
`P = (−4, 6)`: **198 ordered pairs, both slots, zero failures**, with 8 further pairs removed by
the two chord guards and at least one of those — `(−4, 6)` against `(25/4, −75/8)`, whose chord
lands on `(0,0)` — returning the non-square product `0`, so the guards are load-bearing rather
than defensive.  That is evidence for the statement, not a proof of it.  Open here.* -/
def TheGeneralChordClosesTheFace : Prop :=
  ∀ x₁ y₁ x₂ y₂ : ℚ, y₁ ^ 2 = x₁ ^ 3 - 25 * x₁ → y₂ ^ 2 = x₂ ^ 3 - 25 * x₂ →
    y₁ ≠ 0 → y₂ ≠ 0 → x₁ ≠ x₂ →
    chordX x₁ y₁ x₂ y₂ ≠ 0 → chordX x₁ y₁ x₂ y₂ ≠ 5 →
    RankOne.SqCls (chordX x₁ y₁ x₂ y₂) (x₁ * x₂) ∧
    RankOne.SqCls (chordX x₁ y₁ x₂ y₂ - 5) ((x₁ - 5) * (x₂ - 5))

/-! ## 8. The translation lift, at point level

The coordinate identities above are joined to `WeierstrassCurve.Affine.Point` for the family they
cover.  This is not the general homomorphism — it is the statement that for a chord through a
half-turn the group sum really is the point whose abscissa is `translatedX`. -/

private lemma someEqSome {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : Descent.E.Nonsingular x₁ y₁} {h₂ : Descent.E.Nonsingular x₂ y₂} :
    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : Descent.E.Point) =
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-- **The translated coordinates are a point of the curve.**  Mathlib's `nonsingular_add`
transported along `theChordCoordinateIsMathlibsAddX`; without this the lift below would be a
statement about a point that might not exist. -/
theorem theTranslatedCoordinatesAreNonsingular {x y e : ℚ} (hP : Descent.E.Nonsingular x y)
    (hT : Descent.E.Nonsingular e 0) (hxe : x ≠ e) :
    Descent.E.Nonsingular (translatedX x y e)
      (Descent.E.addY x e y (Descent.E.slope x e y 0)) := by
  rw [← theChordCoordinateIsMathlibsAddX x y e hxe]
  exact WeierstrassCurve.Affine.nonsingular_add hP hT fun hxy => hxe hxy.left

/-- **The coordinate law lifts to the point group, on the half-turn family.**  For a point of
`Descent.E` and a half-turn with a different abscissa, the group sum computed by mathlib's own
`Point.add` *is* the point at `translatedX x y e`.  With
`theFaceLawClosesOnEveryHalfTurnTranslation` and `theTranslatedPointIsNeverAHalfTurn` this
discharges the half-turn coset of `Descent.TheFaceIsAHomomorphismEverywhere` — that proposition
stays open because its quantifier ranges over *all* pairs, and the general chord below is the
family that remains. -/
theorem theTranslationIsTheGroupSum {x y e : ℚ} (hP : Descent.E.Nonsingular x y)
    (hT : Descent.E.Nonsingular e 0) (hxe : x ≠ e) :
    (WeierstrassCurve.Affine.Point.some x y hP + WeierstrassCurve.Affine.Point.some e 0 hT :
        Descent.E.Point)
      = WeierstrassCurve.Affine.Point.some (translatedX x y e)
        (Descent.E.addY x e y (Descent.E.slope x e y 0))
        (theTranslatedCoordinatesAreNonsingular hP hT hxe) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxe]
  exact someEqSome (theChordCoordinateIsMathlibsAddX x y e hxe) rfl

end Soma.Holonics.Millennium.FaithfulFace
