import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# A checked exact-pair face of the projective Swing

The primary carrier is the undivided numerator--denominator pair. Division is one affine
chart of that carrier, not its identity. Ordered block transport is checked over arbitrary
rings, including noncommuting matrix entries; the scalar affine/cross-ratio results use a
field. An inverse-domain proof specifies a mathematical chart, not an executable inverse
or its cost. A concrete codec uses its actual inverse construction and retains singular fibres.
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

variable {R : Type*} [Ring R]

/-- The undivided two-entry carrier under an ordered `2 × 2` block transport.  The order is
left multiplication on the pair; no division or determinant is used. -/
def RatioPresentation.blockTransport (A B C D : R) (p : RatioPresentation R) :
    RatioPresentation R :=
  ⟨A * p.num + B * p.den, C * p.num + D * p.den⟩

/-- Common right multiplication, available in noncommutative carriers. -/
def RatioPresentation.rightScale (p : RatioPresentation R) (u : R) : RatioPresentation R :=
  ⟨p.num * u, p.den * u⟩

/-- Ordered block composition: the later block multiplies the earlier block on the left. -/
theorem RatioPresentation.blockTransport_comp
    (A B C D E F G H : R) (p : RatioPresentation R) :
    (RatioPresentation.blockTransport E F G H
      (RatioPresentation.blockTransport A B C D p)) =
      RatioPresentation.blockTransport (E * A + F * C) (E * B + F * D)
        (G * A + H * C) (G * B + H * D) p := by
  apply RatioPresentation.ext <;>
    simp [RatioPresentation.blockTransport]
  · noncomm_ring
  · noncomm_ring

/-- Block transport commutes with common right multiplication, retaining the full pair even when
the affine denominator is singular. -/
theorem RatioPresentation.blockTransport_rightScale
    (A B C D : R) (p : RatioPresentation R) (u : R) :
    RatioPresentation.blockTransport A B C D (p.rightScale u) =
      (RatioPresentation.blockTransport A B C D p).rightScale u := by
  apply RatioPresentation.ext <;>
    simp [RatioPresentation.blockTransport, RatioPresentation.rightScale]
  · noncomm_ring
  · noncomm_ring

/-- The affine fractional chart is available only when the transformed denominator is explicitly a
unit.  The undivided `blockTransport` remains available when it is singular. -/
noncomputable def RatioPresentation.fractionalChart
    (A B C D : R) (p : RatioPresentation R)
    (denominatorUnit : IsUnit (C * p.num + D * p.den)) : R :=
  (A * p.num + B * p.den) * (↑(denominatorUnit.unit⁻¹) : R)

/-- The fractional chart is the right-division statement certified by the retained unit
denominator; no determinant criterion is used. -/
theorem RatioPresentation.fractionalChart_mul_denominator
    (A B C D : R) (p : RatioPresentation R)
    (denominatorUnit : IsUnit (C * p.num + D * p.den)) :
    p.fractionalChart A B C D denominatorUnit *
        (C * p.num + D * p.den) = A * p.num + B * p.den := by
  unfold RatioPresentation.fractionalChart
  have hunit : (↑(denominatorUnit.unit⁻¹) : R) *
      (C * p.num + D * p.den) = 1 := by
    calc
      (↑(denominatorUnit.unit⁻¹) : R) * (C * p.num + D * p.den) =
          (↑(denominatorUnit.unit⁻¹) : R) * (↑denominatorUnit.unit : R) := by
            congr 1
      _ = 1 := by simp
  rw [mul_assoc, hunit, mul_one]

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
