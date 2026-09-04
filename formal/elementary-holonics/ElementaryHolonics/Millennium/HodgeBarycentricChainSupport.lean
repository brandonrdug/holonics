import ElementaryHolonics.Millennium.HodgeBarycentricSubdivisionHomotopy
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Actual finite support of rational singular chains

The cover-smallness theorem already synchronizes every finite addressed simplex family.  This file
exposes the finite family carried by an actual rational singular chain.  The categorical coproduct
is transported to its concrete dependent direct sum, whose support is finite by construction; the
complete coefficients and simplex addresses reconstruct the original chain exactly.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricChainSupport

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricCoverSmallness

/-- Concrete coefficient population of the categorical singular-chain coproduct. -/
abbrev SphereChainDirectSum (degree : ℕ) :=
  DirectSum (SphereSingularSimplex degree) (fun _ => ℚ)

/-! The singular-chain object is a coproduct only up to the canonical colimit comparison exposed by
the 4.33 simplicial-chain API. -/
noncomputable def sphereChainComparison (degree : ℕ) :
    SphereChain degree ≅ ModuleCat.of ℚ (SphereChainDirectSum degree) := by
  classical
  exact (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj sphereTopCat)
    rationalCoefficient degree).coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit
      (fun _ : SphereSingularSimplex degree => rationalCoefficient))

/-- Exact change of chart from the categorical coproduct to dependent finite support. -/
def sphereChainCoordinates (degree : ℕ) (chain : SphereChain degree) :
    SphereChainDirectSum degree := by
  classical
  exact (sphereChainComparison degree).hom chain

/-- The addressed singular simplices with nonzero coefficients in one actual chain. -/
def sphereChainSupport (degree : ℕ) (chain : SphereChain degree) :
    Finset (SphereSingularSimplex degree) := by
  classical
  exact (sphereChainCoordinates degree chain).support

/-- The coordinate attached to one addressed source simplex. -/
def sphereChainCoefficient (degree : ℕ) (chain : SphereChain degree)
    (simplex : SphereSingularSimplex degree) : ℚ :=
  sphereChainCoordinates degree chain simplex

/-- Membership in the returned occurrence population is exactly nonvanishing of its retained
coefficient. -/
theorem mem_sphereChainSupport_iff_coefficient_ne_zero
    (degree : ℕ) (chain : SphereChain degree)
    (simplex : SphereSingularSimplex degree) :
    simplex ∈ sphereChainSupport degree chain ↔
      sphereChainCoefficient degree chain simplex ≠ 0 := by
  classical
  exact DFinsupp.mem_support_iff

/-- The support aperture is empty exactly when the source chain itself is zero. -/
theorem sphereChainSupport_eq_empty_iff
    (degree : ℕ) (chain : SphereChain degree) :
    sphereChainSupport degree chain = ∅ ↔ chain = 0 := by
  classical
  rw [sphereChainSupport, DFinsupp.support_eq_empty]
  constructor
  · intro hcoordinates
    let comparison := sphereChainComparison degree
    have hzero : comparison.hom chain = 0 := by
      simpa only [sphereChainCoordinates, comparison] using hcoordinates
    rw [← comparison.hom_inv_id_apply chain, hzero]
    exact map_zero (ConcreteCategory.hom comparison.inv)
  · intro hchain
    subst chain
    change (ConcreteCategory.hom
      (ModuleCat.coprodIsoDirectSum
        (fun _ : SphereSingularSimplex degree => rationalCoefficient)).hom) 0 = 0
    exact map_zero _

/-- A nonzero current therefore returns at least one addressed nonzero occurrence. -/
theorem sphereChainSupport_nonempty_of_ne_zero
    (degree : ℕ) (chain : SphereChain degree) (hchain : chain ≠ 0) :
    (sphereChainSupport degree chain).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  exact fun hempty => hchain ((sphereChainSupport_eq_empty_iff degree chain).mp hempty)

/-- The finite support chart reconstructs the original categorical chain exactly. -/
theorem sum_support_sphereChainCoefficient_simplexGenerator
    (degree : ℕ) (chain : SphereChain degree) :
    ∑ simplex ∈ sphereChainSupport degree chain,
        sphereChainCoefficient degree chain simplex • simplexGenerator simplex = chain := by
  classical
  let coordinates := sphereChainCoordinates degree chain
  let comparison := sphereChainComparison degree
  have hcoordinates :
      (∑ simplex ∈ coordinates.support,
        DirectSum.of (fun _ : SphereSingularSimplex degree => ℚ)
          simplex (coordinates simplex)) = coordinates :=
    DirectSum.sum_support_of coordinates
  have hinclusion (simplex : SphereSingularSimplex degree) (coefficient : ℚ) :
      comparison.inv
          (DirectSum.of (fun _ : SphereSingularSimplex degree => ℚ)
            simplex coefficient) =
        coefficient • simplexGenerator simplex := by
    rw [← DirectSum.lof_eq_of ℚ]
    have hmap :=
      (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj sphereTopCat)
        rationalCoefficient degree).comp_coconePointUniqueUpToIso_inv
        (ModuleCat.coproductCoconeIsColimit
          (fun _ : SphereSingularSimplex degree => rationalCoefficient))
        ⟨simplex⟩
    have hvalue := congrArg
      (fun morphism => (ConcreteCategory.hom morphism) coefficient) hmap
    change (ConcreteCategory.hom comparison.inv)
        ((DirectSum.lof ℚ (SphereSingularSimplex degree)
          (fun _ : SphereSingularSimplex degree => ℚ) simplex) coefficient) =
      (Sigma.ι (fun _ : SphereSingularSimplex degree => rationalCoefficient) simplex)
        coefficient at hvalue
    exact hvalue.trans
      (sigmaInjection_eq_smul_simplexGenerator degree simplex coefficient)
  calc
    ∑ simplex ∈ sphereChainSupport degree chain,
        sphereChainCoefficient degree chain simplex • simplexGenerator simplex =
      ∑ simplex ∈ coordinates.support,
        comparison.inv
          (DirectSum.of (fun _ : SphereSingularSimplex degree => ℚ)
            simplex (coordinates simplex)) := by
              simp only [sphereChainSupport, sphereChainCoefficient, coordinates]
              simp_rw [hinclusion]
    _ = comparison.inv
        (∑ simplex ∈ coordinates.support,
          DirectSum.of (fun _ : SphereSingularSimplex degree => ℚ)
            simplex (coordinates simplex)) := by rw [map_sum]
    _ = chain := by
      rw [hcoordinates]
      simpa only [coordinates, sphereChainCoordinates] using
        comparison.hom_inv_id_apply chain

/-- Every actual rational singular two-chain supplies the finite addressed family required by the
uniform cover theorem.  The returned occurrence type is its genuine support, not a chosen list or
an upper bound on its cardinality. -/
theorem exists_scale_chain_support_barycentric_descendants_subordinate
    {ι : Type*} (chain : SphereChain 2) (cover : ι → Set ↑sphereTopCat)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ occurrence : ↑(sphereChainSupport 2 chain),
      ∀ word : List BarycentricTriangleAddress,
        scale ≤ word.length → ∃ index,
          Set.range
            ((TopCat.toSSetObjEquiv sphereTopCat
              (Opposite.op (SimplexCategory.mk 2)) occurrence.1).comp
                (barycentricTriangleWordMap word)) ⊆ cover index := by
  classical
  exact exists_scale_finite_sphereSimplex_family_barycentric_descendants_subordinate
    (fun occurrence : ↑(sphereChainSupport 2 chain) => occurrence.1)
    cover hopen hcovers

section Audit

#print axioms sum_support_sphereChainCoefficient_simplexGenerator
#print axioms mem_sphereChainSupport_iff_coefficient_ne_zero
#print axioms sphereChainSupport_eq_empty_iff
#print axioms sphereChainSupport_nonempty_of_ne_zero
#print axioms exists_scale_chain_support_barycentric_descendants_subordinate

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricChainSupport
