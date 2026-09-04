import ElementaryHolonics.Millennium.FamilyTunnellBrandtRelationKernel

/-!
# Exact quotient-to-neighbor reconstruction

The four-coordinate Brandt atlas is an additive presentation.  Its complete
one-generator relation must be quotiented, rather than discarded, before the
returned neighbor is treated as a rank-three lattice.  This file packages the
generic quotient passage and proves that the range of each source-specific
coordinate hom is exactly the previously constructed rational neighbor
subgroup.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification
open Soma.Holonics.Millennium.FamilyTunnellBrandtRelationKernel

variable {p : ℕ} [Fact p.Prime]

/-- A zero-fibre classification by integral multiples is exactly equality of
the additive kernel with the cyclic relation subgroup. -/
theorem ker_eq_zmultiples_of_eq_zero_iff
    (f : NeighborCoordinates →+ RatTriple) (g : NeighborCoordinates)
    (h : ∀ u, f u = 0 ↔ ∃ k : ℤ, u = k • g) :
    f.ker = AddSubgroup.zmultiples g := by
  ext u
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff, h u]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩

/-- The exact first-isomorphism passage after the cyclic relation has been
identified.  The range subtype retains its embedding in the common rational
ambient receiver. -/
def relationQuotientEquivRange
    (f : NeighborCoordinates →+ RatTriple) (g : NeighborCoordinates)
    (h : ∀ u, f u = 0 ↔ ∃ k : ℤ, u = k • g) :
    NeighborCoordinates ⧸ AddSubgroup.zmultiples g ≃+ f.range :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (ker_eq_zmultiples_of_eq_zero_iff f g h).symm).trans
    (QuotientAddGroup.quotientKerEquivRange f)

/-- Equality of two additive subgroup carriers gives an additive equivalence of
their retained subtypes. -/
def addSubgroupEquivOfEq {A : Type*} [AddGroup A]
    {S T : AddSubgroup A} (h : S = T) : S ≃+ T where
  toFun x := ⟨x.1, by rw [← h]; exact x.2⟩
  invFun x := ⟨x.1, by rw [h]; exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The actual neighbor subgroup selected by a fused source occurrence. -/
def occurrenceNeighborSubgroup (hp2 : p ≠ 2) :
    BrandtNeighborOccurrence (p := p) → AddSubgroup RatTriple
  | .inl d => integralNeighbor (p := p) 32 d
  | .inr d => brandtSecondIntegralNeighbor (p := p) hp2 d

/-- The additive image of a first-source coordinate chart is the complete
actual first Brandt neighbor, not merely a pointwise subset. -/
theorem firstBrandtNeighborHom_range (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) :
    (firstBrandtNeighborHom hp2 d).range = integralNeighbor (p := p) 32 d := by
  ext x
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    apply (mem_firstBrandtNeighbor_iff_coordinates hp2 d _).2
    exact ⟨u, (firstBrandtNeighborHom_apply hp2 d u).symm⟩
  · intro hx
    obtain ⟨u, hu⟩ := (mem_firstBrandtNeighbor_iff_coordinates hp2 d x).1 hx
    exact ⟨u, (firstBrandtNeighborHom_apply hp2 d u).trans hu⟩

/-- The additive image of a second-source coordinate chart is the complete
actual second Brandt neighbor. -/
theorem secondBrandtNeighborHom_range (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) :
    (secondBrandtNeighborHom hp2 d).range =
      brandtSecondIntegralNeighbor (p := p) hp2 d := by
  ext x
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    apply (mem_secondBrandtNeighbor_iff_coordinates hp2 d _).2
    exact ⟨u, (secondBrandtNeighborHom_apply hp2 d u).symm⟩
  · intro hx
    obtain ⟨u, hu⟩ := (mem_secondBrandtNeighbor_iff_coordinates hp2 d x).1 hx
    exact ⟨u, (secondBrandtNeighborHom_apply hp2 d u).trans hu⟩

/-- The fused coordinate image is exactly the actual neighbor subgroup selected
by the retained source-class occurrence. -/
theorem brandtNeighborCoordinateHom_range (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (brandtNeighborCoordinateHom hp2 occurrence).range =
      occurrenceNeighborSubgroup hp2 occurrence := by
  cases occurrence with
  | inl d => exact firstBrandtNeighborHom_range hp2 d
  | inr d => exact secondBrandtNeighborHom_range hp2 d

/-- **EVERY ACTUAL BRANDT NEIGHBOR IS EXACTLY THE QUOTIENT BY ITS ONE RETAINED
RELATION.**  The theorem returns the relation generator, its complete positive
`p` turn, and an additive equivalence from the cyclic quotient to the actual
source-addressed neighbor subgroup. -/
theorem BrandtNeighborOccurrence.relationQuotientEquivNeighbor_exists
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    ∃ g : NeighborCoordinates,
      g.2.2.2 = (p : ℤ) ∧
      Nonempty
        (NeighborCoordinates ⧸ AddSubgroup.zmultiples g ≃+
          occurrenceNeighborSubgroup hp2 occurrence) := by
  obtain ⟨g, hg, hkernel⟩ :=
    FamilyTunnellBrandtRelationKernel.BrandtNeighborOccurrence.relationGenerator_exists
      hp2 occurrence
  refine ⟨g, hg, ?_⟩
  let f := brandtNeighborCoordinateHom hp2 occurrence
  exact ⟨(relationQuotientEquivRange f g hkernel).trans
    (addSubgroupEquivOfEq (brandtNeighborCoordinateHom_range hp2 occurrence))⟩

#print axioms ker_eq_zmultiples_of_eq_zero_iff
#print axioms firstBrandtNeighborHom_range
#print axioms secondBrandtNeighborHom_range
#print axioms brandtNeighborCoordinateHom_range
#print axioms BrandtNeighborOccurrence.relationQuotientEquivNeighbor_exists

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
