import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborQuotient

/-!
# The integral positive quadratic receiver on the Brandt cyclic quotient

The actual neighbor has now been reconstructed as `ℤ⁴ / ℤg`.  This file carries
the source-dependent quadratic receiver back across that exact equivalence.  It
proves that every quotient reading is integral and that the descended rational
form is positive definite.  Thus the next Jones--Pall reduction acts on an
actual integral positive ternary lattice carrier, not on an untyped quotient.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification
open Soma.Holonics.Millennium.FamilyTunnellBrandtRelationKernel
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient

variable {p : ℕ} [Fact p.Prime]

/-- A chosen relation generator is lawful only because the source-specific
existence theorem returns its complete kernel classification. -/
def occurrenceRelationGenerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : NeighborCoordinates :=
  Classical.choose
    (FamilyTunnellBrandtRelationKernel.BrandtNeighborOccurrence.relationGenerator_exists
      hp2 occurrence)

theorem occurrenceRelationGenerator_fourth (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceRelationGenerator hp2 occurrence).2.2.2 = (p : ℤ) :=
  (Classical.choose_spec
    (FamilyTunnellBrandtRelationKernel.BrandtNeighborOccurrence.relationGenerator_exists
      hp2 occurrence)).1

theorem occurrenceRelationGenerator_kernel (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u : NeighborCoordinates) :
    brandtNeighborCoordinateHom hp2 occurrence u = 0 ↔
      ∃ k : ℤ, u = k • occurrenceRelationGenerator hp2 occurrence :=
  (Classical.choose_spec
    (FamilyTunnellBrandtRelationKernel.BrandtNeighborOccurrence.relationGenerator_exists
      hp2 occurrence)).2 u

/-- The chosen exact quotient is additively equivalent to the actual neighbor
selected by the source occurrence. -/
def occurrenceQuotientEquivNeighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    NeighborCoordinates ⧸ AddSubgroup.zmultiples
        (occurrenceRelationGenerator hp2 occurrence) ≃+
      occurrenceNeighborSubgroup hp2 occurrence :=
  (relationQuotientEquivRange
      (brandtNeighborCoordinateHom hp2 occurrence)
      (occurrenceRelationGenerator hp2 occurrence)
      (occurrenceRelationGenerator_kernel hp2 occurrence)).trans
    (addSubgroupEquivOfEq (brandtNeighborCoordinateHom_range hp2 occurrence))

/-- The source quadratic receiver descended to the exact cyclic quotient. -/
def occurrenceQuotientQuadratic (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : NeighborCoordinates ⧸ AddSubgroup.zmultiples
      (occurrenceRelationGenerator hp2 occurrence)) : ℚ :=
  occurrence.quadraticReceiver
    ((occurrenceQuotientEquivNeighbor hp2 occurrence x :
      occurrenceNeighborSubgroup hp2 occurrence) : RatTriple)

/-- Every descended quotient reading is an integer in the rational receiver
chart. -/
theorem occurrenceQuotientQuadratic_is_integer (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : NeighborCoordinates ⧸ AddSubgroup.zmultiples
      (occurrenceRelationGenerator hp2 occurrence)) :
    ∃ N : ℤ, occurrenceQuotientQuadratic hp2 occurrence x = (N : ℚ) := by
  let y := occurrenceQuotientEquivNeighbor hp2 occurrence x
  apply BrandtNeighborOccurrence.neighbor_norm_is_integer hp2 occurrence
  cases occurrence with
  | inl d => exact y.2
  | inr d => exact y.2

/-- Exact rational positivity of the first target receiver. -/
private theorem ratTunnellThirtyTwo_nonnegative (v : RatTriple) :
    0 ≤ ratTunnellQuadratic 32 v := by
  unfold ratTunnellQuadratic
  positivity

private theorem ratTunnellThirtyTwo_eq_zero_iff (v : RatTriple) :
    ratTunnellQuadratic 32 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    change 2 * v.1 ^ 2 + v.2.1 ^ 2 + (32 : ℚ) * v.2.2 ^ 2 = 0 at h
    have hx : v.1 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hy : v.2.1 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hz : v.2.2 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    rcases v with ⟨vx, vy, vz⟩
    simp_all
  · rintro rfl
    norm_num [ratTunnellQuadratic]

/-- Exact completed-square chart for the second rational receiver. -/
private theorem ratBrandtSecondQuadratic_completedSquare (v : RatTriple) :
    ratBrandtSecondQuadratic v =
      2 * v.1 ^ 2 + (2 * v.2.1 + v.2.2) ^ 2 + 8 * v.2.2 ^ 2 := by
  unfold ratBrandtSecondQuadratic
  ring

private theorem ratBrandtSecondQuadratic_nonnegative (v : RatTriple) :
    0 ≤ ratBrandtSecondQuadratic v := by
  rw [ratBrandtSecondQuadratic_completedSquare]
  positivity

private theorem ratBrandtSecondQuadratic_eq_zero_iff (v : RatTriple) :
    ratBrandtSecondQuadratic v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [ratBrandtSecondQuadratic_completedSquare] at h
    have hx : v.1 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg (2 * v.2.1 + v.2.2),
        sq_nonneg v.2.2]
    have hz : v.2.2 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg (2 * v.2.1 + v.2.2),
        sq_nonneg v.2.2]
    have hy : v.2.1 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg (2 * v.2.1 + v.2.2),
        sq_nonneg v.2.2]
    rcases v with ⟨vx, vy, vz⟩
    simp_all
  · rintro rfl
    norm_num [ratBrandtSecondQuadratic]

/-- The descended quotient receiver is nonnegative for every actual source
occurrence. -/
theorem occurrenceQuotientQuadratic_nonnegative (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : NeighborCoordinates ⧸ AddSubgroup.zmultiples
      (occurrenceRelationGenerator hp2 occurrence)) :
    0 ≤ occurrenceQuotientQuadratic hp2 occurrence x := by
  cases occurrence with
  | inl d => exact ratTunnellThirtyTwo_nonnegative _
  | inr d => exact ratBrandtSecondQuadratic_nonnegative _

/-- **THE ACTUAL CYCLIC QUOTIENT CARRIES A POSITIVE-DEFINITE INTEGRAL
QUADRATIC RECEIVER.** -/
theorem occurrenceQuotientQuadratic_eq_zero_iff (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : NeighborCoordinates ⧸ AddSubgroup.zmultiples
      (occurrenceRelationGenerator hp2 occurrence)) :
    occurrenceQuotientQuadratic hp2 occurrence x = 0 ↔ x = 0 := by
  let e := occurrenceQuotientEquivNeighbor hp2 occurrence
  have hpoint :
      occurrence.quadraticReceiver ((e x : occurrenceNeighborSubgroup hp2 occurrence) :
          RatTriple) = 0 ↔
        ((e x : occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) = 0 := by
    cases occurrence with
    | inl d => exact ratTunnellThirtyTwo_eq_zero_iff _
    | inr d => exact ratBrandtSecondQuadratic_eq_zero_iff _
  constructor
  · intro hx
    have hey : e x = 0 := by
      apply Subtype.ext
      exact hpoint.mp hx
    exact e.injective (by simpa using hey)
  · rintro rfl
    cases occurrence <;>
      norm_num [occurrenceQuotientQuadratic,
        BrandtNeighborOccurrence.quadraticReceiver, ratTunnellQuadratic,
        ratBrandtSecondQuadratic]

#print axioms occurrenceRelationGenerator_kernel
#print axioms occurrenceQuotientQuadratic_is_integer
#print axioms occurrenceQuotientQuadratic_nonnegative
#print axioms occurrenceQuotientQuadratic_eq_zero_iff

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
