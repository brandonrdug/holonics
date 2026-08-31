import ElementaryHolonics.Millennium.FamilyTunnellAdmissibleOrder

/-!
# The norm-one return of a Tunnell `p`-neighbor

The two global Brandt classes are separated by a geometric receiver: the first
class has a vector of norm one and the second class does not.  This file builds
the source side of that receiver directly from the already constructed integral
`p`-neighbors.

An occurrence of a neighbor is retained in the form

`x = m + (a/p) v`,

where `m` lies in the polar kernel and `v` is the corrected `p²`-isotropic
direction lift.  Its integral numerator is the addressed vector

`u = p m + a v`.

The main theorem proves exactly

`Q(u) = p² Q(x)`.

Consequently every norm-one occurrence returns an integral representation of
`p²`, and reduction of its numerator remains on the original projective
direction.  This is the finite double-cover plate whose fibre count supplies the
Brandt sign.  No modular-form or ideal-class theorem is assumed here.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace Soma.Holonics.Millennium.FamilyTunnellNormOneReturn

open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector

variable {p : ℕ} [Fact p.Prime]

/-- A short owner-local name prevents the substantial projective-subtype chart
from being repeatedly normalized by the elaborator. -/
abbrev FirstDirection :=
  ProjectiveConicDirection (p := p) ((32 : ℤ) : ZMod p)

def firstAdjustedLift (d : FirstDirection (p := p)) : IntTriple :=
  adjustedDirectionLift (p := p) (32 : ℤ) d

def firstIntegralNeighbor (d : FirstDirection (p := p)) : AddSubgroup RatTriple :=
  integralNeighbor (p := p) (32 : ℤ) d

/-- The integral numerator of one retained neighbor coordinate occurrence. -/
def neighborNumerator (m : IntTriple) (a : ℤ) (v : IntTriple) : IntTriple :=
  ((p : ℤ) * m.1 + a * v.1,
    (p : ℤ) * m.2.1 + a * v.2.1,
    (p : ℤ) * m.2.2 + a * v.2.2)

/-- Multiplying the rational occurrence by `p` returns its integral numerator,
coordinate by coordinate. -/
theorem intTripleToRat_neighborNumerator (m : IntTriple) (a : ℤ) (v : IntTriple) :
    intTripleToRat (neighborNumerator (p := p) m a v) =
      ratTripleScale (p : ℚ)
        (ratTripleAdd (intTripleToRat m)
          (ratTripleScale ((a : ℚ) / (p : ℚ)) (intTripleToRat v))) := by
  have hpQ : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply Prod.ext
  · simp [neighborNumerator, intTripleToRat, ratTripleScale, ratTripleAdd]
    field_simp
  · apply Prod.ext <;>
      simp [neighborNumerator, intTripleToRat, ratTripleScale, ratTripleAdd] <;>
      field_simp

/-- Homogeneity of the rational ternary norm. -/
theorem ratTunnellQuadratic_scale (C : ℤ) (r : ℚ) (x : RatTriple) :
    ratTunnellQuadratic C (ratTripleScale r x) =
      r ^ 2 * ratTunnellQuadratic C x := by
  simp [ratTunnellQuadratic, ratTripleScale]
  ring

/-- The integral numerator carries exactly `p²` times the rational neighbor
reading.  This is an equality in `ℚ`, not an integrality estimate. -/
theorem neighborNumerator_quadratic (C : ℤ) (m : IntTriple) (a : ℤ)
    (v : IntTriple) :
    (intTunnellQuadratic C (neighborNumerator (p := p) m a v) : ℚ) =
      (p : ℚ) ^ 2 *
        ratTunnellQuadratic C
          (ratTripleAdd (intTripleToRat m)
            (ratTripleScale ((a : ℚ) / (p : ℚ)) (intTripleToRat v))) := by
  rw [← ratTunnellQuadratic_scale C (p : ℚ)]
  rw [← intTripleToRat_neighborNumerator]
  simp [ratTunnellQuadratic, intTunnellQuadratic, intTripleToRat]

/-- Reduction of the numerator retains the projective direction and only changes
its scalar coordinate. -/
theorem reduce_neighborNumerator (m : IntTriple) (a : ℤ) (v : IntTriple) :
    reduceTriple (p := p) (neighborNumerator (p := p) m a v) =
      scaleCoordinateTriple (a : ZMod p) (reduceTriple (p := p) v) := by
  apply Prod.ext
  · simp [neighborNumerator, reduceTriple, scaleCoordinateTriple]
  · apply Prod.ext <;>
      simp [neighborNumerator, reduceTriple, scaleCoordinateTriple]

/-! ## The retained norm-one reconstruction return -/

/-- **EVERY RETAINED NORM-ONE NEIGHBOR COORDINATE RETURNS AN EXACT
INTEGRAL REPRESENTATION OF `p²`.**

The hypotheses are the complete source coordinate rather than a Boolean
membership shadow. -/
theorem normOneNeighborCoordinate_returns_prime_sq
    (C : ℤ) (m : IntTriple) (a : ℤ) (v : IntTriple) (x : RatTriple)
    (hcoordinate : x =
      ratTripleAdd (intTripleToRat m)
        (ratTripleScale ((a : ℚ) / (p : ℚ)) (intTripleToRat v)))
    (hnorm : ratTunnellQuadratic C x = 1) :
    intTunnellQuadratic C (neighborNumerator (p := p) m a v) =
      (p : ℤ) ^ 2 := by
  have h := neighborNumerator_quadratic (p := p) C m a v
  rw [← hcoordinate, hnorm] at h
  norm_num at h
  exact_mod_cast h

/-- For the actual corrected neighbor generator, the returned numerator lies on
the addressed projective direction after reduction. -/
theorem reduce_firstNeighborNumerator
    (hp2 : p ≠ 2)
    (d : FirstDirection (p := p))
    (m : IntTriple) (a : ℤ) :
    reduceTriple (p := p)
        (neighborNumerator (p := p) m a (firstAdjustedLift d)) =
      scaleCoordinateTriple (a : ZMod p) (projectiveDirectionVector d.1) := by
  unfold firstAdjustedLift
  rw [reduce_neighborNumerator, reduce_adjustedDirectionLift (p := p) hp2]

/-! ## The zero-middle-coordinate branch returns norm one directly -/

def middleUnit : IntTriple := (0, 1, 0)

@[simp] theorem middleUnit_quadratic : intTunnellQuadratic 32 middleUnit = 1 := by
  norm_num [middleUnit, intTunnellQuadratic]

@[simp] theorem middleUnit_rational_quadratic :
    ratTunnellQuadratic 32 (intTripleToRat middleUnit) = 1 := by
  norm_num [middleUnit, ratTunnellQuadratic, intTripleToRat]

/-- If the direction has zero middle coordinate, the pre-existing integral norm-one
axis is in its polar kernel and hence in the neighbor. -/
theorem middleUnit_mem_neighbor_of_direction_middle_eq_zero
    (hp2 : p ≠ 2)
    (d : FirstDirection (p := p))
    (hy : (projectiveDirectionVector d.1).2.1 = 0) :
    intTripleToRat middleUnit ∈ firstIntegralNeighbor d := by
  unfold firstIntegralNeighbor
  apply intTripleToRat_mem_integralNeighbor_of_polar_zero (p := p) hp2
  rw [intTunnellPolar]
  simp [middleUnit]
  have hreduce := congrArg (fun w : CoordinateTriple (ZMod p) => w.2.1)
    (reduce_adjustedDirectionLift (p := p) hp2 32 d)
  simp [reduceTriple] at hreduce
  rw [hreduce, hy]
  simp

/-- The zero-middle-coordinate branch is an inhabited norm-one reconstruction
fibre, not merely a Boolean class label. -/
theorem exists_middleNormOneOccurrence
    (hp2 : p ≠ 2)
    (d : FirstDirection (p := p))
    (hy : (projectiveDirectionVector d.1).2.1 = 0) :
    ∃ x : RatTriple,
      x ∈ firstIntegralNeighbor d ∧ ratTunnellQuadratic 32 x = 1 := by
  exact ⟨intTripleToRat middleUnit,
    middleUnit_mem_neighbor_of_direction_middle_eq_zero hp2 d hy,
    middleUnit_rational_quadratic⟩

/-! ## Norm one separates the two global Brandt lattices -/

/-- The first Brandt lattice has exactly the two oriented middle-axis units at
norm one. -/
theorem brandtFirstQuadratic_eq_one_iff (m : IntTriple) :
    brandtFirstQuadratic m = 1 ↔
      m = (0, 1, 0) ∨ m = (0, -1, 0) := by
  constructor
  · intro h
    have hx2 : m.1 ^ 2 = 0 := by
      have hx0 : 0 ≤ m.1 ^ 2 := sq_nonneg m.1
      have hy0 : 0 ≤ m.2.1 ^ 2 := sq_nonneg m.2.1
      have hz0 : 0 ≤ m.2.2 ^ 2 := sq_nonneg m.2.2
      unfold brandtFirstQuadratic at h
      omega
    have hz2 : m.2.2 ^ 2 = 0 := by
      have hx0 : 0 ≤ m.1 ^ 2 := sq_nonneg m.1
      have hy0 : 0 ≤ m.2.1 ^ 2 := sq_nonneg m.2.1
      have hz0 : 0 ≤ m.2.2 ^ 2 := sq_nonneg m.2.2
      unfold brandtFirstQuadratic at h
      omega
    have hx : m.1 = 0 := by simpa using (sq_eq_zero_iff.mp hx2)
    have hz : m.2.2 = 0 := by simpa using (sq_eq_zero_iff.mp hz2)
    have hy2 : m.2.1 ^ 2 = 1 := by
      unfold brandtFirstQuadratic at h
      rw [hx, hz] at h
      norm_num at h ⊢
      exact h
    rcases sq_eq_one_iff.mp hy2 with hy | hy
    · left
      apply Prod.ext
      · exact hx
      · apply Prod.ext <;> assumption
    · right
      apply Prod.ext
      · exact hx
      · apply Prod.ext <;> assumption
  · rintro (rfl | rfl) <;> norm_num [brandtFirstQuadratic]

/-- The second Brandt lattice has no norm-one occurrence.  The completed-square
chart makes the separation geometric: the `8z²`, `2x²`, and square terms leave
no integral route to one. -/
theorem brandtSecondQuadratic_ne_one (m : IntTriple) :
    brandtSecondQuadratic m ≠ 1 := by
  intro h
  have hcompleted := brandtSecondQuadratic_completedSquare m
  have hform :
      2 * m.1 ^ 2 + (2 * m.2.1 + m.2.2) ^ 2 + 8 * m.2.2 ^ 2 = 1 := by
    omega
  have hz2 : m.2.2 ^ 2 = 0 := by
    have hx0 : 0 ≤ m.1 ^ 2 := sq_nonneg m.1
    have hm0 : 0 ≤ (2 * m.2.1 + m.2.2) ^ 2 :=
      sq_nonneg (2 * m.2.1 + m.2.2)
    have hz0 : 0 ≤ m.2.2 ^ 2 := sq_nonneg m.2.2
    omega
  have hz : m.2.2 = 0 := by simpa using (sq_eq_zero_iff.mp hz2)
  rw [hz] at hform
  norm_num at hform
  have hx2 : m.1 ^ 2 = 0 := by
    have hx0 : 0 ≤ m.1 ^ 2 := sq_nonneg m.1
    have hm0 : 0 ≤ (2 * m.2.1) ^ 2 := sq_nonneg (2 * m.2.1)
    omega
  rw [hx2] at hform
  have hsquare : (2 * m.2.1) ^ 2 = 1 := by omega
  rcases sq_eq_one_iff.mp hsquare with hy | hy <;> omega

#print axioms neighborNumerator_quadratic
#print axioms reduce_neighborNumerator
#print axioms normOneNeighborCoordinate_returns_prime_sq
#print axioms reduce_firstNeighborNumerator
#print axioms middleUnit_mem_neighbor_of_direction_middle_eq_zero
#print axioms exists_middleNormOneOccurrence
#print axioms brandtFirstQuadratic_eq_one_iff
#print axioms brandtSecondQuadratic_ne_one

end Soma.Holonics.Millennium.FamilyTunnellNormOneReturn
