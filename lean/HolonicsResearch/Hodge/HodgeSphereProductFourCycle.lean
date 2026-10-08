import HolonicsResearch.Hodge.HodgeSphereProductReconstruction

/-!
# The explicit sphere-product four-cycle

[agent-inferred] This is one mathematical owner moved from HodgeProductDiagonal.
Its declarations occur once with unchanged bodies, statements and scope; the
next complete owner consumes its checked maps. No partial-source acceptance
is used for the public nonboundary consumer.
-/

noncomputable section

namespace Holonics.Hodge.HodgeProductDiagonal

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Holonics.DiagonalChainTransport
open Holonics.Hodge.HodgeProjectiveLineSingularReduction
open Holonics.Hodge.HodgeSphereProductFiniteComplex
open Holonics.Hodge.HodgeTwoSphereFundamentalCycle
open Holonics.Hodge.HodgeSphereProductRulingProjections
open Holonics.Hodge.HodgeSphereHomologyEquivalence
open Holonics.Hodge.HodgeSphereFundamentalDetector

universe u

/-! ## The genuine product four-current from two retained sphere cycles -/

/-- The degree-four separated boundary is the sum of the two actual factor-incidence actions.
This equation supplies the consumer of the signed shuffle law without assuming a cellular
reduction or a homology dimension. -/
theorem pairTwoBoundary_factor_incidence {X Y : SSet}
    (current : Current (Simplex X 2 × Simplex Y 2)) :
    pairTwoBoundary X Y current =
      leftMiddleAxis (mapPairLeft (factorBoundary X 1) current) +
        rightMiddleAxis (mapPairRight (factorBoundary Y 1) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single occurrence coefficient =>
      rcases occurrence with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp [pairTwoBoundary, pairTwoBoundaryAtom, mapPairLeft_generator,
        mapPairRight_generator, factorBoundary, factorBoundaryAtom,
        leftMiddleAxis, rightMiddleAxis, Fin.sum_univ_three]
      module

/-- Two closed factor two-currents return a closed, genuinely addressed product four-current.
The second incidence has positive sign because the first factor has even degree. -/
theorem pairTwoShuffle_closed {X Y : SSet}
    (left : FactorCurrent X 2) (right : FactorCurrent Y 2)
    (hleft : factorBoundary X 1 left = 0)
    (hright : factorBoundary Y 1 right = 0) :
    diagonalBoundaryFour X Y (pairTwoShuffle X Y (pairCurrent left right)) = 0 := by
  have law := LinearMap.congr_fun (boundary_pairTwoShuffle X Y)
    (pairCurrent left right)
  change diagonalBoundaryFour X Y (pairTwoShuffle X Y (pairCurrent left right)) =
    rejoinThree X Y (pairTwoBoundary X Y (pairCurrent left right)) at law
  rw [pairTwoBoundary_factor_incidence, mapPairLeft_pairCurrent,
    mapPairRight_pairCurrent, hleft, hright, pairCurrent_zero_left,
    pairCurrent_zero_right, map_zero, map_zero, zero_add, map_zero] at law
  exact law

/-- The complete five addressed simplex faces compute the genuine product boundary in degree
four.  This uses the existing coproduct chart, rather than inserting a new chain carrier. -/
theorem productChainDiagonalEquiv_boundary_four_generator (simplex : ProductSimplex 4) :
    productChainDiagonalEquiv 3
        (SphereProductSingularChainComplex.d 4 3 (productSimplexGenerator simplex)) =
      diagonalBoundaryFour SphereSSet SphereSSet
        (productChainDiagonalEquiv 4 (productSimplexGenerator simplex)) := by
  rw [boundary_productSimplexGenerator, map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_generator]
  change (∑ omitted : Fin 5, (-1 : ℚ) ^ (omitted : ℕ) •
      generator (splitProductSimplex (productSimplexFace omitted simplex))) =
    diagonalBoundaryFour SphereSSet SphereSSet (generator (splitProductSimplex simplex))
  simp only [diagonalBoundaryFour, extend_generator, diagonalBoundaryFourAtom,
    splitProductSimplex_face]
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, one_smul, neg_one_smul, add_zero, zero_add] <;> abel

/-- The actual singular boundary and diagonal current boundary agree on every four-current. -/
theorem productChainDiagonalEquiv_boundary_four (chain : ProductChain 4) :
    productChainDiagonalEquiv 3 (SphereProductSingularChainComplex.d 4 3 chain) =
      diagonalBoundaryFour SphereSSet SphereSSet (productChainDiagonalEquiv 4 chain) := by
  let left : ProductChain 4 →ₗ[ℚ] Current (DiagonalOccurrence SphereSSet SphereSSet 3) :=
    (productChainDiagonalEquiv 3).toLinearMap.comp
      (SphereProductSingularChainComplex.d 4 3).hom
  let right : ProductChain 4 →ₗ[ℚ] Current (DiagonalOccurrence SphereSSet SphereSSet 3) :=
    (diagonalBoundaryFour SphereSSet SphereSSet).comp
      (productChainDiagonalEquiv 4).toLinearMap
  have mapsEqual : left = right := by
    apply LinearMap.ext
    intro current
    rw [← productCurrent_chain_roundtrip 4 current]
    have extended : left.comp (productCurrentToChain 4) =
        right.comp (productCurrentToChain 4) := by
      apply Finsupp.lhom_ext
      intro simplex coefficient
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [LinearMap.comp_apply, map_smul, productCurrentToChain_generator]
      exact congrArg (coefficient • ·)
        (productChainDiagonalEquiv_boundary_four_generator simplex)
    exact LinearMap.congr_fun extended (chainToProductCurrent 4 current)
  exact LinearMap.congr_fun mapsEqual chain

/-- [agent-inferred] The genuine degree-four product source is the complete signed shuffle of
the two retained tetrahedral sphere fundamental currents.  It contains four face choices in each
factor and six shuffles per pair, rather than a pulled-back cellular unit. -/
def sphereProductFundamentalFourChain : ProductChain 4 :=
  (productChainDiagonalEquiv 4).symm
    (pairTwoShuffle SphereSSet SphereSSet
      (pairCurrent
        (topologicalChainEquivCurrent sphereTopCat 2 sphereFundamentalCandidate)
        (topologicalChainEquivCurrent sphereTopCat 2 sphereFundamentalCandidate)))

/-- The explicit product source is closed in the actual rational singular complex. Closure is
proved here independently of the normalized nonboundary receiver constructed below. -/
theorem sphereProductFundamentalFourChain_closed :
    SphereProductSingularChainComplex.d 4 3 sphereProductFundamentalFourChain = 0 := by
  apply (productChainDiagonalEquiv 3).injective
  rw [map_zero, productChainDiagonalEquiv_boundary_four,
    sphereProductFundamentalFourChain, LinearEquiv.apply_symm_apply]
  apply pairTwoShuffle_closed
  all_goals
    rw [← topologicalChainEquivCurrent_boundary,
      sphereFundamentalCandidate_boundary_zero, map_zero]

section Audit

#print axioms pairTwoBoundary_factor_incidence
#print axioms pairTwoShuffle_closed
#print axioms productChainDiagonalEquiv_boundary_four_generator
#print axioms productChainDiagonalEquiv_boundary_four
#print axioms sphereProductFundamentalFourChain_closed

end Audit

end Holonics.Hodge.HodgeProductDiagonal
