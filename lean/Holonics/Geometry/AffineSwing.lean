import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# Affine point reflection

The frozen-board chart of a projective swing is the point reflection about its anchor. This
elementary affine operation and its group laws live in Geometry so receiver-relative geometric
consequences do not need to import the Research realization that motivated the name.
-/

namespace Holonics.Geometry.AffineSwing

variable {G : Type*} [AddCommGroup G]

/-- The affine half-turn of `a` about the declared anchor `b`. -/
def swing (b a : G) : G := b + b - a

/-- A point reflection negates displacement from its anchor. -/
theorem theSwingNegatesTheDisplacementFromTheAnchor (b a : G) :
    swing b a - b = -(a - b) := by
  simp only [swing]; abel

/-- Two point reflections about the same anchor return the original point. -/
theorem theSwingIsAnInvolution (b : G) : Function.Involutive (swing b) := by
  intro a; simp only [swing]; abel

/-- The anchor is fixed by its point reflection. -/
@[simp] theorem theAnchorIsFixed (b : G) : swing b b = b := by
  simp [swing]

/-- Two point reflections about different anchors compose to a doubled translation. -/
theorem twoSwingsAreADoubledTranslation (b c a : G) :
    swing b (swing c a) = a + (b + b - (c + c)) := by
  simp only [swing]; abel

/-- Reversing two distinct point reflections changes the result by the doubled anchor offset. -/
theorem theSwingsDoNotCommute (b c a : G) :
    swing b (swing c a) - swing c (swing b a) =
      (b + b - (c + c)) - (c + c - (b + b)) := by
  simp only [swing]; abel

end Holonics.Geometry.AffineSwing
