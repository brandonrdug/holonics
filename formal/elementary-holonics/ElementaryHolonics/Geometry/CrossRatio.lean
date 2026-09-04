import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A checked exact-pair face of the projective Swing

The primary carrier is the undivided numerator--denominator pair.  Division is
one affine chart of that carrier, not its identity.  The Typst synopsis contains
the full Möbius derivation; this cell checks affine transport exactly and does
not claim to have formalized the whole projective-line library.
-/

namespace Soma.Holonics

/-- An exact ratio presentation before a quotient receiver is selected. -/
structure RatioPresentation (K : Type*) where
  num : K
  den : K
deriving DecidableEq

@[ext]
theorem RatioPresentation.ext
    {K : Type*} {p q : RatioPresentation K}
    (hnum : p.num = q.num) (hden : p.den = q.den) :
    p = q := by
  cases p
  cases q
  simp_all

variable {K : Type*} [Field K]

/-- Common scaling retains a projective ratio presentation when nonzero. -/
def RatioPresentation.scale (u : K) (p : RatioPresentation K) :
    RatioPresentation K :=
  ⟨u * p.num, u * p.den⟩

/--
Cross multiplication compares exact ratio presentations without performing
division.  Degenerate `(0, 0)` pairs require a separate admissibility boundary
before this relation is promoted to equality in a projective line.
-/
def RatioPresentation.ProjectivelyEq
    (p q : RatioPresentation K) : Prop :=
  p.num * q.den = q.num * p.den

/-- The ordered Swing carrier before any quotient is taken. -/
def swingPair (a b c d : K) : RatioPresentation K :=
  ⟨(c - a) * (d - b), (c - b) * (d - a)⟩

/-- The scalar cross-ratio is one quotient receiver of `swingPair`. -/
def crossRatio (a b c d : K) : K :=
  (swingPair a b c d).num / (swingPair a b c d).den

theorem ratioPresentation_projectivelyEq_scale
    (u : K) (p : RatioPresentation K) :
    (p.scale u).ProjectivelyEq p := by
  simp [RatioPresentation.ProjectivelyEq, RatioPresentation.scale]
  ring

/--
Every affine coordinate change transports both Swing coordinates by the same
exact square.  No division and no nonzero hypothesis is needed for this pair
identity.
-/
theorem swingPair_affine_coordinates
    (a b c d u v : K) :
    swingPair (u * a + v) (u * b + v) (u * c + v) (u * d + v) =
      (swingPair a b c d).scale (u * u) := by
  apply RatioPresentation.ext <;>
    simp only [swingPair, RatioPresentation.scale,
      add_sub_add_right_eq_sub, ← mul_sub] <;>
    ring

theorem swingPair_affine_projectively
    (a b c d u v : K) :
    RatioPresentation.ProjectivelyEq
      (swingPair (u * a + v) (u * b + v) (u * c + v) (u * d + v))
      (swingPair a b c d) := by
  rw [swingPair_affine_coordinates]
  exact ratioPresentation_projectivelyEq_scale (u * u) (swingPair a b c d)

theorem crossRatio_affine
    (a b c d u v : K)
    (hu : u ≠ 0)
    (hcb : c - b ≠ 0)
    (hda : d - a ≠ 0) :
    crossRatio (u * a + v) (u * b + v) (u * c + v) (u * d + v) =
      crossRatio a b c d := by
  simp only [crossRatio, swingPair, add_sub_add_right_eq_sub, ← mul_sub]
  field_simp [hu, hcb, hda]

end Soma.Holonics
