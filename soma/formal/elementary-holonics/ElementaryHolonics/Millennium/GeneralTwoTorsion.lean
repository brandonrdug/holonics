import ElementaryHolonics.Millennium.GeneralMordell

/-!
# GeneralTwoTorsion: the four two-torsion points and the halving fibre

Step three of the ordered worktrack.  Two facts the descent leans on implicitly and
which are worth having explicitly:

* **`theTwoTorsionIsExactlyTheFourPoints`** — on `y² = x(x−a)(x−b)` a point is killed
  by two exactly when it is the identity or has ordinate zero, and the ordinates
  vanish exactly at the three roots.  So `E[2](ℚ) = {O, (0,0), (a,0), (b,0)}`, of
  order four, and the two-torsion is entirely rational — which is what puts this
  family in the descent's reach at all.
* **`theHalvingFibreIsATorsor`** — a nonempty halving fibre is a torsor for `E[2]`:
  translating one half by a two-torsion point gives another, and any two halves differ
  by one.  So a point that is a double is a double in exactly four ways.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralTwoTorsion

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace

variable {a b : ℚ}

/-! ## 1. The two-torsion is exactly the four points -/

/-- A point is killed by two exactly when it is the identity or its ordinate
vanishes. -/
theorem theTwoTorsionIsTheVanishingOrdinate (P : (E a b).Point) :
    P + P = 0 ↔ (P = 0 ∨ ∃ (x : ℚ) (h : (E a b).Nonsingular x 0), P = Point.some h) := by
  constructor
  · intro h
    rcases P with _ | @⟨x, y, hns⟩
    · exact Or.inl rfl
    · right
      have hneg : (Point.some hns : (E a b).Point) = -Point.some hns := by
        rw [eq_neg_iff_add_eq_zero]
        exact h
      rw [Point.neg_some] at hneg
      have hy : y = (E a b).negY x y := by
        have := congrArg (fun P => match P with
          | Point.zero => (0 : ℚ)
          | Point.some (y := yy) _ => yy) hneg
        simpa using this
      simp only [negY, E] at hy
      have hy0 : y = 0 := by linarith
      subst hy0
      exact ⟨x, hns, rfl⟩
  · rintro (rfl | ⟨x, hns, rfl⟩)
    · simp
    · refine Point.add_self_of_Y_eq ?_
      simp only [negY, E]
      ring

/-- **THE TWO-TORSION IS EXACTLY THE FOUR POINTS**: the identity and the three roots.
The two-torsion of this family is entirely rational, which is what puts it in the
descent's reach. -/
theorem theTwoTorsionIsExactlyTheFourPoints (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a - b ≠ 0) (P : (E a b).Point) :
    P + P = 0 ↔ (P = 0 ∨
      (∃ h : (E a b).Nonsingular 0 0, P = Point.some h) ∨
      (∃ h : (E a b).Nonsingular a 0, P = Point.some h) ∨
      (∃ h : (E a b).Nonsingular b 0, P = Point.some h)) := by
  rw [theTwoTorsionIsTheVanishingOrdinate]
  constructor
  · rintro (rfl | ⟨x, hns, rfl⟩)
    · exact Or.inl rfl
    · have hcurve := onCurve hns
      have hroots : x * (x - a) * (x - b) = 0 := by linear_combination -hcurve
      rcases mul_eq_zero.mp hroots with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · subst h''
          exact Or.inr (Or.inl ⟨hns, rfl⟩)
        · have : x = a := by linarith [sub_eq_zero.mp h'']
          subst this
          exact Or.inr (Or.inr (Or.inl ⟨hns, rfl⟩))
      · have : x = b := by linarith [sub_eq_zero.mp h']
        subst this
        exact Or.inr (Or.inr (Or.inr ⟨hns, rfl⟩))
  · rintro (rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, h, rfl⟩
    · exact Or.inr ⟨a, h, rfl⟩
    · exact Or.inr ⟨b, h, rfl⟩

/-! ## 2. The halving fibre is a torsor -/

/-- **THE HALVING FIBRE IS A TORSOR FOR THE TWO-TORSION**: translating a half by a
two-torsion point gives another half, and any two halves differ by a two-torsion
point.  A point that is a double is a double in exactly `|E[2]|` ways. -/
theorem theHalvingFibreIsATorsor (P Q Q' : (E a b).Point) (T : (E a b).Point)
    (hT : T + T = 0) (hQ : Q + Q = P) :
    ((Q + T) + (Q + T) = P) ∧ ((Q' + Q' = P) → (Q' - Q) + (Q' - Q) = 0) := by
  constructor
  · calc (Q + T) + (Q + T) = (Q + Q) + (T + T) := by abel
      _ = P + 0 := by rw [hQ, hT]
      _ = P := add_zero P
  · intro hQ'
    calc (Q' - Q) + (Q' - Q) = (Q' + Q') - (Q + Q) := by abel
      _ = P - P := by rw [hQ, hQ']
      _ = 0 := sub_self P

/-- **THE HALVES ARE THE TRANSLATES**: given one half, every half is that one
translated by a two-torsion point, and every such translate is a half.  This is the
reconstruction fibre of the descent, exhibited. -/
theorem theHalvesAreExactlyTheTranslates (P Q : (E a b).Point) (hQ : Q + Q = P)
    (Q' : (E a b).Point) :
    Q' + Q' = P ↔ ∃ T : (E a b).Point, T + T = 0 ∧ Q' = Q + T := by
  constructor
  · intro hQ'
    refine ⟨Q' - Q, ?_, by abel⟩
    exact (theHalvingFibreIsATorsor P Q Q' 0 (by simp) hQ).2 hQ'
  · rintro ⟨T, hT, rfl⟩
    exact (theHalvingFibreIsATorsor P Q Q T hT hQ).1

end Soma.Holonics.Millennium.GeneralTwoTorsion
