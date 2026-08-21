import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# RankOne: the descent face meets a point of infinite order

Deed D2 of the BSD route chart.  The congruent-number curve for five, `y² = x³ − 25x`, has rank
one: five **is** a congruent number (the `(3/2, 20/3, 41/6)` triangle), and the realized
population strictly exceeds the torsion.  This file computes that excess through mathlib's
actual group law, exactly over `ℚ`:

* the three half-turn points `(0,0)`, `(5,0)`, `(−5,0)` are nonsingular and are half-turns;
* the new point `P = (−4, 6)` is on the curve, and its **double is computed through the tangent
  case of the group law**: `2P = (1681/144, −62279/1728)`;
* `P` and `2P` are distinct from the identity and from every half-turn — the realized chain
  visibly leaves the torsion table;
* the **descent face** `P ↦ (x, x − 5)` mod squares separates `P` from all four torsion images —
  the separations carried by `−1` and `5` failing to be rational squares;
* and **the face reads the double as trivial, exactly as the descent homomorphism predicts**:
  both slots of `2P` are literal rational squares — `x(2P) = (41/12)²` and
  `x(2P) − 5 = (31/12)²`.  The open homomorphism proposition's consistency arrives as a
  computed witness, not an assumption.

What this measures, in the route's vocabulary: on the rank-zero curve of `Descent.lean` the
descent face's image was exactly the torsion classes; here the face takes a **fifth value** on a
computed point whose double it reads as trivial.  The realized population has a direction the
torsion cannot supply.  **Infinite order itself is carried as a named open proposition** — its
classical proof runs through the torsion classification (reduction, or Mazur), which is imported
mathematics with no mathlib owner and is not smuggled in here.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims movement on
the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.RankOne

open WeierstrassCurve.Affine

/-- The congruent-number curve for five: `y² = x³ − 25x`. -/
def E5 : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -25, 0⟩

/-! ## 1. The five points, nonsingular on the curve -/

theorem nonsingular00 : E5.Nonsingular 0 0 := by
  simp [E5]

theorem nonsingular50 : E5.Nonsingular 5 0 := by
  rw [nonsingular_iff, equation_iff]; norm_num [E5]

theorem nonsingularNeg50 : E5.Nonsingular (-5) 0 := by
  rw [nonsingular_iff, equation_iff]; norm_num [E5]

theorem nonsingularP : E5.Nonsingular (-4) 6 := by
  rw [nonsingular_iff, equation_iff]; norm_num [E5]

theorem nonsingular2P : E5.Nonsingular (1681/144) (-62279/1728) := by
  rw [nonsingular_iff, equation_iff]; norm_num [E5]

/-- The identity-adjacent torsion candidates and the new chain. -/
def T0 : E5.Point := .some nonsingular00
def T5 : E5.Point := .some nonsingular50
def Tm5 : E5.Point := .some nonsingularNeg50
def P : E5.Point := .some nonsingularP
def P2 : E5.Point := .some nonsingular2P

/-! ## 2. The half-turns, and the doubling of the new point -/

/-- The three torsion candidates are half-turns, through the group law's vertical case. -/
theorem theThreePointsAreHalfTurns : T0 + T0 = 0 ∧ T5 + T5 = 0 ∧ Tm5 + Tm5 = 0 :=
  ⟨Point.add_self_of_Y_eq (by simp [E5]),
   Point.add_self_of_Y_eq (by simp [E5]),
   Point.add_self_of_Y_eq (by simp [E5])⟩

private lemma some_eq_some {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : E5.Nonsingular x₁ y₁} {h₂ : E5.Nonsingular x₂ y₂} :
    (Point.some h₁ : E5.Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

/-- **The double of the new point, computed through the tangent case**: the tangent at
`(−4, 6)` has slope `23/12`, and the group law returns `(1681/144, −62279/1728)` — the point
whose `x`-coordinate is the square `(41/12)²` behind the `(3/2, 20/3, 41/6)` triangle of area
five. -/
theorem theDoubleIsComputed : P + P = P2 := by
  have hy : (6 : ℚ) ≠ E5.negY (-4) 6 := by norm_num [E5]
  have hs : E5.slope (-4) (-4) 6 6 = 23/12 := by
    rw [slope_of_Y_ne rfl hy]; norm_num [E5]
  show Point.some nonsingularP + Point.some nonsingularP = Point.some nonsingular2P
  rw [Point.add_self_of_Y_ne hy]
  exact some_eq_some (by rw [hs]; norm_num [E5]) (by rw [hs]; norm_num [E5])

/-! ## 3. The descent face on this curve -/

/-- The first slot: `x`, with the classical convention `(0−5)(0+5) = −25` at the vanishing
coordinate. -/
def slotOne : E5.Point → ℚ
  | .zero => 1
  | .some (x := x) _ => if x = 0 then -25 else x

/-- The second slot: `x − 5`, with the convention `(5−0)(5+5) = 50` at its vanishing
coordinate. -/
def slotTwo : E5.Point → ℚ
  | .zero => 1
  | .some (x := x) _ => if x = 5 then 50 else x - 5

/-- The face values on the five points: `0 ↦ (1,1)`, `(0,0) ↦ (−25,−5)`, `(5,0) ↦ (5,50)`,
`(−5,0) ↦ (−5,−10)`, `P ↦ (−4,−9)`, `2P ↦ ((41/12)², (31/12)²)`. -/
theorem theFaceValues :
    (slotOne 0 = 1 ∧ slotTwo 0 = 1) ∧
    (slotOne T0 = -25 ∧ slotTwo T0 = -5) ∧
    (slotOne T5 = 5 ∧ slotTwo T5 = 50) ∧
    (slotOne Tm5 = -5 ∧ slotTwo Tm5 = -10) ∧
    (slotOne P = -4 ∧ slotTwo P = -9) ∧
    (slotOne P2 = 1681/144 ∧ slotTwo P2 = 961/144) := by
  refine ⟨⟨rfl, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [slotOne, slotTwo, T0, T5, Tm5, P, P2]

/-- **The chain leaves the torsion table**: `P` and `2P` are distinct from the identity and from
every half-turn, read off the face's first slot. -/
theorem theChainLeavesTheTorsionTable :
    (P ≠ 0 ∧ P ≠ T0 ∧ P ≠ T5 ∧ P ≠ Tm5) ∧
    (P2 ≠ 0 ∧ P2 ≠ T0 ∧ P2 ≠ T5 ∧ P2 ≠ Tm5) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg slotOne h;
     norm_num [slotOne, T0, T5, Tm5, P, P2] at this)

/-! ## 4. The separations, carried by two non-squares -/

/-- Two rationals in one square class. -/
def SqCls (a b : ℚ) : Prop := ∃ c : ℚ, c ≠ 0 ∧ a = c ^ 2 * b

theorem notSquareFive : ¬ IsSquare (5 : ℚ) := by
  rw [show (5 : ℚ) = ((5 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  exact (by norm_num : Nat.Prime 5).not_isSquare

/-- **The face separates the new point from every torsion image.**  Against the identity and
`(5,0)` the first slot fails by sign; against `(0,0)` the first slots agree (`−4 = (2/5)²·(−25)`,
the square class genuinely working) and the second slot fails through five; against `(−5,0)` the
first slot fails through five. -/
theorem theFaceSeparatesTheNewPoint :
    ¬ SqCls (slotOne P) (slotOne 0) ∧
    ¬ SqCls (slotTwo P) (slotTwo T0) ∧
    ¬ SqCls (slotOne P) (slotOne T5) ∧
    ¬ SqCls (slotOne P) (slotOne Tm5) := by
  obtain ⟨⟨e1, -⟩, ⟨a1, a2⟩, ⟨b1, -⟩, ⟨c1, -⟩, ⟨p1, p2⟩, -⟩ := theFaceValues
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p1, e1]
    rintro ⟨c, -, h⟩
    nlinarith [sq_nonneg c]
  · rw [p2, a2]
    rintro ⟨c, hc, h⟩
    have h95 : 5 * c ^ 2 = 9 := by linarith
    refine notSquareFive ⟨3 / c, ?_⟩
    field_simp
    linarith [h95]
  · rw [p1, b1]
    rintro ⟨c, -, h⟩
    nlinarith [sq_nonneg c]
  · rw [p1, c1]
    rintro ⟨c, hc, h⟩
    have h54 : 5 * c ^ 2 = 4 := by linarith
    refine notSquareFive ⟨2 / c, ?_⟩
    field_simp
    linarith [h54]

/-- **The face reads the double as trivial, as the descent homomorphism predicts**: both slots
of `2P` are literal rational squares.  A doubled point lands in the trivial square class, and
here it does so by exhibited square roots — the open homomorphism proposition's consistency,
returned as computation. -/
theorem theDoubledSlotsAreSquares :
    IsSquare (slotOne P2) ∧ IsSquare (slotTwo P2) := by
  obtain ⟨-, -, -, -, -, ⟨q1, q2⟩⟩ := theFaceValues
  constructor
  · exact ⟨41/12, by rw [q1]; norm_num⟩
  · exact ⟨31/12, by rw [q2]; norm_num⟩

/-! ## 5. The open half, named and never claimed -/

/-- **The new point has infinite order.**  Classically true — the torsion of `y² = x³ − n²x` is
the Klein four-group, by reduction or by Mazur's theorem, neither in mathlib — and the face
separation above is exactly the descent evidence for it.  Open here. -/
def ThePointHasInfiniteOrder : Prop :=
  ∀ n : ℕ, 0 < n → n • P ≠ 0

/-- **The torsion is the Klein four-group**: the points of finite order are exactly the identity
and the three half-turns.  Classical; open here. -/
def TheTorsionIsTheKleinGroup : Prop :=
  ∀ Q : E5.Point, (∃ n : ℕ, 0 < n ∧ n • Q = 0) ↔ (Q = 0 ∨ Q = T0 ∨ Q = T5 ∨ Q = Tm5)

/-- **The face is a homomorphism on the whole point group** of this curve — the multiplicativity
half of the descent injection, as on the rank-zero curve.  Classical; open here.  Given it and
the torsion classification, `theFaceSeparatesTheNewPoint` shows `P` lies outside
`torsion + 2·E5(ℚ)`, which is the descent's certificate that the realized population exceeds the
torsion. -/
def TheFaceIsAHomomorphismEverywhere : Prop :=
  ∀ Q R : E5.Point,
    SqCls (slotOne (Q + R)) (slotOne Q * slotOne R) ∧
    SqCls (slotTwo (Q + R)) (slotTwo Q * slotTwo R)

end Soma.Holonics.Millennium.RankOne
