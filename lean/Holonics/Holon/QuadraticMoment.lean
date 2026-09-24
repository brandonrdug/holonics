import Mathlib.Data.Matrix.Basic

/-!
# Holon.QuadraticMoment: finite weighted quadratic storage and reception

The finite weighted second-moment carrier and its exact bilinear receiver contraction.  This
module is independent of Holon.Element so that storage instances can depend on both owners without
creating an import cycle.
-/

noncomputable section

namespace Holonics.Millennium.HolonicQuadraticMomentCondensation

open scoped BigOperators

variable {Scalar Support Cell : Type*}
  [CommRing Scalar] [Fintype Support] [Fintype Cell]

/-- The exact weighted second moment of a finite current family. -/
def quadraticMoment
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    Matrix Cell Cell Scalar :=
  fun left right => ∑ support, weight support * current support left * current support right

/-- Contract a moment field with one declared bilinear receiver. -/
def contractMoment
    (receiver moment : Matrix Cell Cell Scalar) : Scalar :=
  ∑ left, ∑ right, receiver left right * moment left right

/-- The corresponding support-by-support receiver before moment condensation. -/
def enumerateQuadraticReceiver
    (receiver : Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) : Scalar :=
  ∑ support, weight support *
    (∑ left, ∑ right, receiver left right * current support left * current support right)

/-- Every finite quadratic receiver is exactly a contraction of the second-moment field. -/
theorem contract_quadraticMoment_eq_enumerateQuadraticReceiver
    (receiver : Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    contractMoment receiver (quadraticMoment weight current) =
      enumerateQuadraticReceiver receiver weight current := by
  simp only [contractMoment, quadraticMoment, enumerateQuadraticReceiver]
  simp_rw [Finset.mul_sum]
  calc
    (∑ left, ∑ right, ∑ support,
        receiver left right * (weight support * current support left * current support right)) =
        ∑ left, ∑ support, ∑ right,
          receiver left right * (weight support * current support left * current support right) := by
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.sum_comm]
    _ = ∑ support, ∑ left, ∑ right,
          receiver left right * (weight support * current support left * current support right) := by
      rw [Finset.sum_comm]
    _ = ∑ support, ∑ left, ∑ right,
          weight support * (receiver left right * current support left * current support right) := by
      apply Finset.sum_congr rfl
      intro support _
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      ring

end Holonics.Millennium.HolonicQuadraticMomentCondensation
