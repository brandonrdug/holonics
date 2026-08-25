import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic

/-!
# Coordinate-subset receivers

The near/far decomposition of an `n`-coordinate receiver is the Boolean cube of coordinate
subsets.  A member of the subset records exactly the coordinates on which an Abel difference is
used; its complement records the coordinates retained in the local near window.  This owner is
independent of every analytic specialization.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.CoordinateSubsetReceiver

/-- One face of the coordinate receiver cube. -/
abbrev CoordinateFace (n : ℕ) := Finset (Fin n)

/-- The complete Boolean population of coordinate faces. -/
def coordinateFaces (n : ℕ) : Finset (CoordinateFace n) :=
  Finset.univ.powerset

@[simp]
theorem mem_coordinateFaces {n : ℕ} (face : CoordinateFace n) :
    face ∈ coordinateFaces n := by
  simp [coordinateFaces]

/-- An `n`-coordinate near/far receiver has exactly `2^n` faces. -/
theorem card_coordinateFaces (n : ℕ) :
    (coordinateFaces n).card = 2 ^ n := by
  simp [coordinateFaces]

/-- The three-coordinate receiver used by the torus kernel has exactly eight faces. -/
theorem card_coordinateFaces_three :
    (coordinateFaces 3).card = 8 := by
  norm_num [card_coordinateFaces]

/-- Active coordinates receive a second difference; inactive coordinates retain order zero. -/
def differenceOrder {n : ℕ} (face : CoordinateFace n) (axis : Fin n) : ℕ :=
  if axis ∈ face then 2 else 0

@[simp]
theorem differenceOrder_of_mem {n : ℕ} {face : CoordinateFace n} {axis : Fin n}
    (haxis : axis ∈ face) :
    differenceOrder face axis = 2 := by
  simp [differenceOrder, haxis]

@[simp]
theorem differenceOrder_of_not_mem {n : ℕ} {face : CoordinateFace n} {axis : Fin n}
    (haxis : axis ∉ face) :
    differenceOrder face axis = 0 := by
  simp [differenceOrder, haxis]

/-- The complementary face records precisely the near-window coordinates. -/
def nearFace {n : ℕ} (face : CoordinateFace n) : CoordinateFace n :=
  faceᶜ

@[simp]
theorem mem_nearFace_iff {n : ℕ} {face : CoordinateFace n} {axis : Fin n} :
    axis ∈ nearFace face ↔ axis ∉ face := by
  simp [nearFace]

@[simp]
theorem card_face_add_card_nearFace {n : ℕ} (face : CoordinateFace n) :
    face.card + (nearFace face).card = n := by
  simp [nearFace]

/-- The scale exponent carried by a three-coordinate subset mass.  Each active second
difference removes two radial powers from the undifferenced three-dimensional population. -/
def threeDimensionalMassExponent (face : CoordinateFace 3) : ℤ :=
  3 - 2 * face.card

@[simp]
theorem threeDimensionalMassExponent_empty :
    threeDimensionalMassExponent (∅ : CoordinateFace 3) = 3 := by
  simp [threeDimensionalMassExponent]

theorem threeDimensionalMassExponent_singleton (axis : Fin 3) :
    threeDimensionalMassExponent ({axis} : CoordinateFace 3) = 1 := by
  simp [threeDimensionalMassExponent]

theorem threeDimensionalMassExponent_pair
    (first second : Fin 3) (haxes : first ≠ second) :
    threeDimensionalMassExponent ({first, second} : CoordinateFace 3) = -1 := by
  simp [threeDimensionalMassExponent, haxes]

@[simp]
theorem threeDimensionalMassExponent_univ :
    threeDimensionalMassExponent (Finset.univ : CoordinateFace 3) = -3 := by
  native_decide

/-- The near-window volume exponent and the far Abel-denominator exponent cancel the subset-mass
exponent exactly. -/
theorem threeDimensional_exponent_balance (face : CoordinateFace 3) :
    threeDimensionalMassExponent face + face.card - (nearFace face).card = 0 := by
  rw [threeDimensionalMassExponent]
  have hcard := card_face_add_card_nearFace face
  omega

section Audit

#print axioms card_coordinateFaces_three
#print axioms threeDimensional_exponent_balance

end Audit

end Soma.Holonics.CoordinateSubsetReceiver
