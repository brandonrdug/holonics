import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# The half-turn (affine point reflection)

The half-turn `S_a x = 2a − x` about an anchor `a` is one move of the Swing, the move about a grip
(`docs/ELEMENTARY_OBJECTS.md#the-swing`): the move `x ↦ M x + b` with `M = −1`, whose pivot is its
anchor (`Geometry/Motion.swing_is_half_turn_move`, `swing_pivot_is_anchor`). It is the
frozen-board chart of harmonic conjugation (`Geometry/Swing`). The definition keeps its historical
name `swing`. This elementary affine operation and its group laws live in Geometry so
receiver-relative geometric consequences do not need to import the Research realization that
motivated the name.
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

/-- Two half-turns about different anchors compose to a doubled translation. This is the length-two
case of the half-turn word law, whose owner is `Geometry/Motion.swing_word_linear_part` (every
word has linear part `(−1)^length`; `even_swing_word_is_translation`). It stays here, beside the
definition that `Motion` imports, for its consumers. -/
theorem twoSwingsAreADoubledTranslation (b c a : G) :
    swing b (swing c a) = a + (b + b - (c + c)) := by
  simp only [swing]; abel

/-- Reversing two distinct point reflections changes the result by the doubled anchor offset. -/
theorem theSwingsDoNotCommute (b c a : G) :
    swing b (swing c a) - swing c (swing b a) =
      (b + b - (c + c)) - (c + c - (b + b)) := by
  simp only [swing]; abel

end Holonics.Geometry.AffineSwing
