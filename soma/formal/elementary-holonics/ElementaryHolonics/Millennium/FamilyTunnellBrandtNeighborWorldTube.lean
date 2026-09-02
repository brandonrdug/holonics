import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighbors

/-!
# One addressed carrier for both Tunnell--Brandt neighbor classes

The two Brandt classes previously owned separate projective-direction and
integral-neighbor constructions.  This file fuses them only at their common
typed port: source class, projective direction, corrected integral lift, actual
rational neighbor lattice, quadratic receiver, and integrality return.

The carrier has exactly two copies of the `p+1` projective aperture.  It does
not assign a destination class.  That absent map is now visible as the precise
next geometric edge rather than being hidden by an aggregate cardinality.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube

open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors

variable {p : ℕ} [Fact p.Prime]

/-- The retained global integral class at the source end of a neighbor span. -/
inductive BrandtClass
  | first
  | second
  deriving DecidableEq

instance : Fintype BrandtClass :=
  ⟨{BrandtClass.first, BrandtClass.second}, fun x => by cases x <;> simp⟩

/-- First-class projective directions use the diagonal `32` chart. -/
abbrev FirstBrandtDirection :=
  ProjectiveConicDirection (p := p) ((32 : ℤ) : ZMod p)

/-- Second-class projective directions use the exact cross-term transport of
the diagonal `8` chart. -/
abbrev SecondBrandtDirection :=
  BrandtSecondProjectiveDirection (p := p)

/-- One addressed odd-prime neighbor occurrence.  The sum retains the source
class instead of flattening the two direction populations. -/
abbrev BrandtNeighborOccurrence :=
  FirstBrandtDirection (p := p) ⊕ SecondBrandtDirection (p := p)

def BrandtNeighborOccurrence.sourceClass
    (occurrence : BrandtNeighborOccurrence (p := p)) : BrandtClass :=
  match occurrence with
  | .inl _ => .first
  | .inr _ => .second

/-- The actual corrected residue direction seen by the source lattice. -/
def BrandtNeighborOccurrence.directionVector (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : CoordinateTriple (ZMod p) :=
  match occurrence with
  | .inl d => projectiveDirectionVector d.1
  | .inr d => brandtSecondDirectionVector hp2 d

/-- Membership in the actual rational integral neighbor lattice returned by
the occurrence.  Keeping membership as the common port avoids unfolding and
rebuilding either already-owned subgroup. -/
def BrandtNeighborOccurrence.neighborMember (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (x : RatTriple) : Prop :=
  match occurrence with
  | .inl d =>
      x ∈ Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors.integralNeighbor
        (p := p) 32 d
  | .inr d => x ∈ brandtSecondIntegralNeighbor hp2 d

/-- The source-dependent rational quadratic receiver. -/
def BrandtNeighborOccurrence.quadraticReceiver
    (occurrence : BrandtNeighborOccurrence (p := p)) : RatTriple → ℚ :=
  match occurrence with
  | .inl _ => ratTunnellQuadratic 32
  | .inr _ => ratBrandtSecondQuadratic

private theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

private theorem thirtyTwo_ne_zero (hp2 : p ≠ 2) :
    ((32 : ℤ) : ZMod p) ≠ 0 := by
  rw [show ((32 : ℤ) : ZMod p) = 2 ^ 5 by norm_num]
  exact pow_ne_zero 5 (two_ne_zero (p := p) hp2)

/-- Each source class has exactly the same `p+1` direction aperture. -/
theorem firstBrandtDirection_card (hp2 : p ≠ 2) :
    Fintype.card (FirstBrandtDirection (p := p)) = p + 1 := by
  exact projectiveConicDirection_fintype_card (p := p) hp2
    (thirtyTwo_ne_zero (p := p) hp2)

theorem secondBrandtDirection_card (hp2 : p ≠ 2) :
    Fintype.card (SecondBrandtDirection (p := p)) = p + 1 :=
  brandtSecondProjectiveDirection_card (p := p) hp2

/-- The complete source world-tube therefore has exactly two retained copies
of the projective aperture. -/
theorem brandtNeighborOccurrence_card (hp2 : p ≠ 2) :
    Fintype.card (BrandtNeighborOccurrence (p := p)) = 2 * (p + 1) := by
  rw [Fintype.card_sum, firstBrandtDirection_card (p := p) hp2,
    secondBrandtDirection_card (p := p) hp2]
  omega

/-- Every retained source direction is genuinely isotropic for its own
quadratic receiver. -/
theorem BrandtNeighborOccurrence.directionVector_isotropic (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    match occurrence with
    | .inl _ =>
        reducedTunnellQuadratic ((32 : ℤ) : ZMod p)
          (occurrence.directionVector hp2) = 0
    | .inr _ => reducedBrandtSecondQuadratic (occurrence.directionVector hp2) = 0 := by
  cases occurrence with
  | inl d =>
      exact projectiveDirectionVector_isotropic d
  | inr d =>
      exact brandtSecondDirectionVector_isotropic hp2 d

/-- Every quadratic reading on either actual neighbor lattice is integral.
This is the common returned constitutive law of the fused carrier. -/
theorem BrandtNeighborOccurrence.neighbor_norm_is_integer
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    {x : RatTriple}
    (hx : BrandtNeighborOccurrence.neighborMember hp2 occurrence x) :
    ∃ N : ℤ,
      BrandtNeighborOccurrence.quadraticReceiver occurrence x = (N : ℚ) := by
  cases occurrence with
  | inl d =>
      exact integralNeighbor_norm_is_integer (p := p) hp2 32 d hx
  | inr d =>
      exact brandtSecondIntegralNeighbor_norm_is_integer (p := p) hp2 d hx

#print axioms firstBrandtDirection_card
#print axioms brandtNeighborOccurrence_card
#print axioms BrandtNeighborOccurrence.directionVector_isotropic
#print axioms BrandtNeighborOccurrence.neighbor_norm_is_integer

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
