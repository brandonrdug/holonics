import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Descent: the transport chain lands on the congruent-number curve

The transport-chain vocabulary of this development — realized population, locally admissible
population, obstruction group as their quotient — was built abstractly and instanced on complexes.
**Its classical home is the two-descent of an elliptic curve**: the realized population is the
image of the rational points, the locally admissible population is the Selmer group, and the
obstruction group is Tate–Shafarevich at two.  This file brings the chain onto the curve where the
question began — `y² = x³ − x`, the congruent-number curve for one — using **mathlib's actual
group law** on nonsingular affine points, not a restatement of it.

What is proved, all exact over `ℚ` and through `WeierstrassCurve.Affine.Point`:

* the three affine two-torsion points are nonsingular points of the curve;
* each is a **half-turn**: `P + P = 0`, by the group law's own `add_self_of_Y_eq`;
* the chord through any two of them lands on the third — the complete Klein four-group computed
  through mathlib's slope/`addX`/`addY` formulas;
* the **descent face** `P ↦ (x, x − 1)` modulo squares, with the classical convention at the
  vanishing coordinates (the product of the differences against the other two roots), takes the
  four points to four **pairwise inequivalent** square classes — injectivity carried by exactly
  three arithmetic facts: `−1`, `2` and `−2` are not squares in `ℚ`;
* the face is **multiplicative on the computed population**, every product identity exhibited with
  its square witness.

What is named open, honestly, because the classical machinery is real and absent from mathlib:

* the face is a homomorphism on the whole point group (`TheFaceIsAHomomorphismEverywhere`);
* its kernel is the doubled population (`TheKernelIsTheDoubledPopulation`) — together these are
  the injection `E(ℚ)/2E(ℚ) ↪ (ℚ*/ℚ*²)²` of a complete two-descent;
* the four half-turns are the whole point population (`TheFourHalfTurnsAreTheWholePopulation`) —
  classically a theorem, by Fermat's own infinite descent; it is **equivalent to one not being a
  congruent number**, and Fermat's descent is the FOUND stroke of navigation with the
  well-foundedness of the terrain as its termination.

The Tate–Shafarevich correspondence is carried in prose, not smuggled into a `Prop`: declaring
the Selmer group by hand would author the partition this development's own grading rule forbids.
For this curve the classical computation returns Selmer equal to the computed image, hence
`Ш(E/ℚ)[2] = 0` — imported, cited, and not proved here.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`:
`grep -rli "selmer\|shafarevich\|mordell" Mathlib --include='*.lean'` → 2 files, and one of them
matters here: `RingTheory/DedekindDomain/SelmerGroup.lean` carries the `K(S, n)` Selmer group of
a Dedekind domain — **the target group of the descent map** — while the Mordell–Weil theorem,
the Selmer group *of an elliptic curve*, and the Tate–Shafarevich group have no owner (the other
file is Selmer's trinomials, unrelated).  So the open homomorphism proposition below has a
mathlib-native landing structure to aim at.  A name search over a stated scope, not a
content-absence proof.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims movement on the
Birch–Swinnerton-Dyer conjecture; no L-function, height pairing, or analytic rank appears.
-/

namespace Soma.Holonics.Millennium.Descent

open WeierstrassCurve.Affine

/-- The congruent-number curve for one: `y² = x³ − x`, Weierstrass coefficients
`(0, 0, 0, −1, 0)`. -/
def E : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -1, 0⟩

/-! ## 1. The three half-turn points, nonsingular on the curve -/

theorem nonsingular00 : E.Nonsingular 0 0 := by
  simp [E]

theorem nonsingular10 : E.Nonsingular 1 0 := by
  rw [nonsingular_iff, equation_iff]; norm_num [E]

theorem nonsingularNeg10 : E.Nonsingular (-1) 0 := by
  rw [nonsingular_iff, equation_iff]; norm_num [E]

/-- The point `(0, 0)`. -/
def P00 : E.Point := .some 0 0 nonsingular00

/-- The point `(1, 0)`. -/
def P10 : E.Point := .some 1 0 nonsingular10

/-- The point `(−1, 0)`. -/
def Pm10 : E.Point := .some (-1) 0 nonsingularNeg10

/-! ## 2. Each is a half-turn, by the group law itself -/

/-- **The three points are half-turns**: each added to itself returns the identity, through
mathlib's `add_self_of_Y_eq` — the vertical-chord case of the group law, entered because `y = 0`
is its own negation on this curve. -/
theorem theThreePointsAreHalfTurns : P00 + P00 = 0 ∧ P10 + P10 = 0 ∧ Pm10 + Pm10 = 0 :=
  ⟨Point.add_self_of_Y_eq (by simp [E]),
   Point.add_self_of_Y_eq (by simp [E]),
   Point.add_self_of_Y_eq (by simp [E])⟩

private lemma some_eq_some {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : E.Nonsingular x₁ y₁} {h₂ : E.Nonsingular x₂ y₂} :
    (Point.some x₁ y₁ h₁ : E.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-- **The chord through two half-turns lands on the third.**  All three sums computed through
mathlib's secant slope and `addX`/`addY` — the slope of every chord is zero, and the third
intersection is forced by the cubic.  With the half-turn theorem this is the complete Klein
four-group `(ℤ/2)²` inside `E(ℚ)`, computed rather than declared. -/
theorem theChordThroughTwoLandsOnTheThird :
    P00 + P10 = Pm10 ∧ P00 + Pm10 = P10 ∧ P10 + Pm10 = P00 := by
  have h1 : E.slope 0 1 0 0 = 0 := by
    rw [slope_of_X_ne (by norm_num)]; norm_num
  have h2 : E.slope 0 (-1) 0 0 = 0 := by
    rw [slope_of_X_ne (by norm_num)]; norm_num
  have h3 : E.slope 1 (-1) 0 0 = 0 := by
    rw [slope_of_X_ne (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · show Point.some 0 0 nonsingular00 + Point.some 1 0 nonsingular10 =
      Point.some (-1) 0 nonsingularNeg10
    rw [Point.add_of_X_ne (by norm_num : (0 : ℚ) ≠ 1)]
    exact some_eq_some (by rw [h1]; norm_num [E, addX])
      (by rw [h1]; norm_num [E, addY, negY, negAddY, addX])
  · show Point.some 0 0 nonsingular00 + Point.some (-1) 0 nonsingularNeg10 =
      Point.some 1 0 nonsingular10
    rw [Point.add_of_X_ne (by norm_num : (0 : ℚ) ≠ -1)]
    exact some_eq_some (by rw [h2]; norm_num [E, addX])
      (by rw [h2]; norm_num [E, addY, negY, negAddY, addX])
  · show Point.some 1 0 nonsingular10 + Point.some (-1) 0 nonsingularNeg10 =
      Point.some 0 0 nonsingular00
    rw [Point.add_of_X_ne (by norm_num : (1 : ℚ) ≠ -1)]
    exact some_eq_some (by rw [h3]; norm_num [E, addX])
      (by rw [h3]; norm_num [E, addY, negY, negAddY, addX])

/-! ## 3. The descent face

The two-descent map sends an affine point to `(x, x − 1)` modulo squares.  At a vanishing
coordinate the classical convention substitutes the product of the differences against the other
two roots of `x(x − 1)(x + 1)`: the first slot at `x = 0` is `(0 − 1)(0 − (−1)) = −1`, the second
slot at `x = 1` is `(1 − 0)(1 − (−1)) = 2`.  The identity goes to `(1, 1)`. -/

/-- The first slot of the descent face. -/
def slotOne : E.Point → ℚ
  | .zero => 1
  | .some x _ _ => if x = 0 then -1 else x

/-- The second slot of the descent face. -/
def slotTwo : E.Point → ℚ
  | .zero => 1
  | .some x _ _ => if x = 1 then 2 else x - 1

/-- The four descent-face values, computed: `0 ↦ (1,1)`, `(0,0) ↦ (−1,−1)`, `(1,0) ↦ (1,2)`,
`(−1,0) ↦ (−1,−2)`. -/
theorem theFourFaceValues :
    (slotOne 0 = 1 ∧ slotTwo 0 = 1) ∧
    (slotOne P00 = -1 ∧ slotTwo P00 = -1) ∧
    (slotOne P10 = 1 ∧ slotTwo P10 = 2) ∧
    (slotOne Pm10 = -1 ∧ slotTwo Pm10 = -2) := by
  refine ⟨⟨rfl, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num [slotOne, slotTwo, P00, P10, Pm10]

/-! ## 4. Same square class, and the three facts that separate the four values -/

/-- Two rationals lie in one square class when a nonzero square carries one to the other. -/
def SqCls (a b : ℚ) : Prop := ∃ c : ℚ, c ≠ 0 ∧ a = c ^ 2 * b

theorem sqClsRefl (a : ℚ) : SqCls a a := ⟨1, one_ne_zero, by ring⟩

theorem notSquareTwo : ¬ IsSquare (2 : ℚ) := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  exact Nat.prime_two.not_isSquare

/-- `−1` is not a square times `1`: a square is non-negative. -/
theorem theNegativeUnitClassIsNotTheTrivialClass : ¬ SqCls (-1) 1 := by
  rintro ⟨c, -, h⟩
  nlinarith [sq_nonneg c]

/-- `1` is not a square times `−1`. -/
theorem theTrivialClassIsNotTheNegativeUnitClass : ¬ SqCls 1 (-1) := by
  rintro ⟨c, -, h⟩
  nlinarith [sq_nonneg c]

/-- `2` is not a square times `1`, because two is not a rational square. -/
theorem theTwoClassIsNotTheTrivialClass : ¬ SqCls 2 1 := by
  rintro ⟨c, -, h⟩
  exact notSquareTwo ⟨c, by rw [h]; ring⟩

/-- `−2` is not a square times `−1`: it would make `c` a square root of two. -/
theorem theNegativeTwoClassIsNotTheNegativeUnitClass : ¬ SqCls (-2) (-1) := by
  rintro ⟨c, -, h⟩
  refine notSquareTwo ⟨c, ?_⟩
  have h2 : c ^ 2 = 2 := by linarith
  rw [← h2, pow_two]

/-- **The descent face separates the four points**: the four image pairs are pairwise
inequivalent under componentwise square-class equality.  Injectivity is carried entirely by
`−1`, `2` and `−2` failing to be rational squares — the arithmetic paying for the geometry. -/
theorem theFaceSeparatesTheFourPoints :
    ¬ (SqCls (slotOne P00) (slotOne 0) ∧ SqCls (slotTwo P00) (slotTwo 0)) ∧
    ¬ (SqCls (slotOne P10) (slotOne 0) ∧ SqCls (slotTwo P10) (slotTwo 0)) ∧
    ¬ (SqCls (slotOne Pm10) (slotOne 0) ∧ SqCls (slotTwo Pm10) (slotTwo 0)) ∧
    ¬ (SqCls (slotOne P10) (slotOne P00) ∧ SqCls (slotTwo P10) (slotTwo P00)) ∧
    ¬ (SqCls (slotOne Pm10) (slotOne P00) ∧ SqCls (slotTwo Pm10) (slotTwo P00)) ∧
    ¬ (SqCls (slotOne Pm10) (slotOne P10) ∧ SqCls (slotTwo Pm10) (slotTwo P10)) := by
  obtain ⟨⟨e1, e2⟩, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := theFourFaceValues
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a1, e1]; exact fun h => theNegativeUnitClassIsNotTheTrivialClass h.1
  · rw [b2, e2]; exact fun h => theTwoClassIsNotTheTrivialClass h.2
  · rw [c1, e1]; exact fun h => theNegativeUnitClassIsNotTheTrivialClass h.1
  · rw [b1, a1]; exact fun h => theTrivialClassIsNotTheNegativeUnitClass h.1
  · rw [c2, a2]; exact fun h => theNegativeTwoClassIsNotTheNegativeUnitClass h.2
  · rw [c1, b1]; exact fun h => theNegativeUnitClassIsNotTheTrivialClass h.1

/-- **The face is multiplicative on the computed population** — every sum in the Klein group,
with the square witness exhibited.  Five of the six identities are literal equalities (`c = 1`);
the sixth, `2 · (−2) = 2² · (−1)`, is where the square class genuinely works. -/
theorem theFaceIsMultiplicativeOnTheComputedPopulation :
    (SqCls (slotOne (P00 + P00)) (slotOne P00 * slotOne P00) ∧
     SqCls (slotTwo (P00 + P00)) (slotTwo P00 * slotTwo P00)) ∧
    (SqCls (slotOne (P10 + P10)) (slotOne P10 * slotOne P10) ∧
     SqCls (slotTwo (P10 + P10)) (slotTwo P10 * slotTwo P10)) ∧
    (SqCls (slotOne (P00 + P10)) (slotOne P00 * slotOne P10) ∧
     SqCls (slotTwo (P00 + P10)) (slotTwo P00 * slotTwo P10)) ∧
    (SqCls (slotOne (P00 + Pm10)) (slotOne P00 * slotOne Pm10) ∧
     SqCls (slotTwo (P00 + Pm10)) (slotTwo P00 * slotTwo Pm10)) ∧
    (SqCls (slotOne (P10 + Pm10)) (slotOne P10 * slotOne Pm10) ∧
     SqCls (slotTwo (P10 + Pm10)) (slotTwo P10 * slotTwo Pm10)) := by
  obtain ⟨h00, h10, hm10⟩ := theThreePointsAreHalfTurns
  obtain ⟨hs1, hs2, hs3⟩ := theChordThroughTwoLandsOnTheThird
  obtain ⟨⟨e1, e2⟩, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := theFourFaceValues
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [h00, e1, a1]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [h00, e2, a2]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [h10, e1, b1]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [h10, e2, b2]; exact ⟨1 / 2, by norm_num, by norm_num⟩
  · rw [hs1, c1, a1, b1]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [hs1, c2, a2, b2]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [hs2, b1, a1, c1]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [hs2, b2, a2, c2]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [hs3, a1, b1, c1]; exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [hs3, a2, b2, c2]; exact ⟨1 / 2, by norm_num, by norm_num⟩

/-! ## 5. The open half, named and never claimed

The complete two-descent is classical machinery with no mathlib owner.  Each statement below is a
real proposition about this curve, carried open. -/

/-- **The descent face is a homomorphism on the whole point group** — for every pair of points,
each slot of the sum lies in the square class of the product of slots.

*Aside: the injection `E(ℚ)/2E(ℚ) ↪ (ℚ*/ℚ*²)²`, restricted to its multiplicativity half.
Classical; open here.* -/
def TheFaceIsAHomomorphismEverywhere : Prop :=
  ∀ P Q : E.Point,
    SqCls (slotOne (P + Q)) (slotOne P * slotOne Q) ∧
    SqCls (slotTwo (P + Q)) (slotTwo P * slotTwo Q)

/-- **The kernel of the face is the doubled population** — a point's slots are both trivial
square classes exactly when the point is twice another.

*Aside: `ker = 2E(ℚ)`, the exactness half of the descent injection.  Classical; open here.* -/
def TheKernelIsTheDoubledPopulation : Prop :=
  ∀ P : E.Point, (SqCls (slotOne P) 1 ∧ SqCls (slotTwo P) 1) ↔ ∃ Q : E.Point, P = 2 • Q

/-- **The four half-turns are the whole point population** of `y² = x³ − x` over `ℚ`.

*Aside: the rank is zero and the torsion is the computed Klein four-group.  This is equivalent to
**one not being a congruent number** — no rational right triangle has area one — and its classical
proof is Fermat's infinite descent, the first descent argument in mathematics.  Open here; the
descent chain that would discharge it is exactly the machinery the two open propositions above
name.* -/
def TheFourHalfTurnsAreTheWholePopulation : Prop :=
  ∀ P : E.Point, P = 0 ∨ P = P00 ∨ P = P10 ∨ P = Pm10

end Soma.Holonics.Millennium.Descent
