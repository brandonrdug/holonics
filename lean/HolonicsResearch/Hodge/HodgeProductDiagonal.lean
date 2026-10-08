import HolonicsResearch.Hodge.HodgeSphereNormalizedCoefficient

/-!
# The sphere-product nonboundary consumer

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

theorem productChainDiagonalEquiv_boundary_five_generator (simplex : ProductSimplex 5) :
    productChainDiagonalEquiv 4
        (SphereProductSingularChainComplex.d 5 4 (productSimplexGenerator simplex)) =
      diagonalBoundaryFive SphereSSet SphereSSet
        (productChainDiagonalEquiv 5 (productSimplexGenerator simplex)) := by
  rw [boundary_productSimplexGenerator, map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_generator]
  simp only [diagonalBoundaryFive, extend_generator, diagonalBoundaryFiveAtom,
    splitProductSimplex_face]
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, one_smul, neg_one_smul, add_zero, zero_add] <;> abel

theorem productChainDiagonalEquiv_boundary_five (chain : ProductChain 5) :
    productChainDiagonalEquiv 4 (SphereProductSingularChainComplex.d 5 4 chain) =
      diagonalBoundaryFive SphereSSet SphereSSet (productChainDiagonalEquiv 5 chain) := by
  let left := (productChainDiagonalEquiv 4).toLinearMap.comp
    (SphereProductSingularChainComplex.d 5 4).hom
  let right := (diagonalBoundaryFive SphereSSet SphereSSet).comp
    (productChainDiagonalEquiv 5).toLinearMap
  have extended : left.comp (productCurrentToChain 5) =
      right.comp (productCurrentToChain 5) := by
    apply Finsupp.lhom_ext
    intro simplex coefficient
    rw [show Finsupp.single simplex coefficient =
      coefficient • generator simplex by simp [generator]]
    simp only [LinearMap.comp_apply, map_smul, productCurrentToChain_generator]
    exact congrArg (coefficient • ·)
      (productChainDiagonalEquiv_boundary_five_generator simplex)
  have law := LinearMap.congr_fun extended (chainToProductCurrent 5 chain)
  change left chain = right chain
  simpa only [LinearMap.comp_apply, productCurrent_chain_roundtrip] using law

/-- The actual product receiver is the normalized (2,2) Alexander--Whitney coefficient,
transported through the existing singular/diagonal equivalence. -/
def sphereProductFourReceiver : ProductChain 4 →ₗ[ℚ] ℚ :=
  (pairFourReceiver sphereNormalizedSimplexCoefficient sphereNormalizedSimplexCoefficient).comp
    (productChainDiagonalEquiv 4).toLinearMap

theorem sphereProductFourReceiver_boundary (chain : ProductChain 5) :
    sphereProductFourReceiver (SphereProductSingularChainComplex.d 5 4 chain) = 0 := by
  change pairFourReceiver sphereNormalizedSimplexCoefficient sphereNormalizedSimplexCoefficient
    (productChainDiagonalEquiv 4 (SphereProductSingularChainComplex.d 5 4 chain)) = 0
  rw [productChainDiagonalEquiv_boundary_five]
  exact pairFourReceiver_boundaryFive_zero _ _ sphereNormalizedSimplexCoefficient_closed
    sphereNormalizedSimplexCoefficient_closed _

theorem sphereProductFourReceiver_fundamental :
    sphereProductFourReceiver sphereProductFundamentalFourChain = 1 := by
  change pairFourReceiver sphereNormalizedSimplexCoefficient sphereNormalizedSimplexCoefficient
    (productChainDiagonalEquiv 4 sphereProductFundamentalFourChain) = 1
  rw [sphereProductFundamentalFourChain, LinearEquiv.apply_symm_apply,
    pairFourReceiver_pairTwoShuffle_pairCurrent, sphereNormalizedCurrentCoefficient_fundamental]
  norm_num

/-- The explicit 96 signed singular four-simplices cannot be the boundary of any actual
singular five-chain. This is a detector theorem, not an assumed product reduction. -/
theorem sphereProductFundamentalFourChain_not_mem_boundary_range :
    sphereProductFundamentalFourChain ∉
      Set.range (SphereProductSingularChainComplex.d 5 4).hom.toAddMonoidHom := by
  exact Holonics.Foundation.not_mem_range_of_receiver_boundary_eq_zero
    (SphereProductSingularChainComplex.d 5 4).hom.toAddMonoidHom
    sphereProductFourReceiver.toAddMonoidHom sphereProductFourReceiver_boundary
    (by
      change sphereProductFourReceiver sphereProductFundamentalFourChain ≠ 0
      rw [sphereProductFourReceiver_fundamental]
      exact one_ne_zero)

def sphereProductFundamentalFourCycleLift :
    ModuleCat.of ℚ ℚ ⟶ SphereProductSingularChainComplex.cycles 4 :=
  SphereProductSingularChainComplex.liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ sphereProductFundamentalFourChain))
    3 (by simp) (by
      ext
      change SphereProductSingularChainComplex.d 4 3
        ((1 : ℚ) • sphereProductFundamentalFourChain) = 0
      simpa using sphereProductFundamentalFourChain_closed)

theorem sphereProductFundamentalFourCycleLift_i :
    sphereProductFundamentalFourCycleLift ≫ SphereProductSingularChainComplex.iCycles 4 =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ sphereProductFundamentalFourChain) := by
  apply HomologicalComplex.liftCycles_i

def sphereProductFundamentalFourHomologyClass :
    RationalSingularHomology 4 sphereProductTopCat :=
  (sphereProductFundamentalFourCycleLift ≫ SphereProductSingularChainComplex.homologyπ 4) 1

def sphereProductFourReceiverOnCycles :
    SphereProductSingularChainComplex.cycles 4 ⟶ ModuleCat.of ℚ ℚ :=
  SphereProductSingularChainComplex.iCycles 4 ≫ ModuleCat.ofHom sphereProductFourReceiver

theorem sphereProductFourReceiverOnCycles_boundaries :
    SphereProductSingularChainComplex.toCycles 5 4 ≫ sphereProductFourReceiverOnCycles = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro chain
  change sphereProductFourReceiver
      (SphereProductSingularChainComplex.iCycles 4
        (SphereProductSingularChainComplex.toCycles 5 4 chain)) = 0
  have included :
      SphereProductSingularChainComplex.iCycles 4
          (SphereProductSingularChainComplex.toCycles 5 4 chain) =
        SphereProductSingularChainComplex.d 5 4 chain := by
    change (SphereProductSingularChainComplex.toCycles 5 4 ≫
      SphereProductSingularChainComplex.iCycles 4) chain = _
    rw [SphereProductSingularChainComplex.toCycles_i]
  rw [included]
  exact sphereProductFourReceiver_boundary chain

/-- Descend the actual chain receiver through the actual homology quotient. -/
def sphereProductFourReceiverOnHomology :
    RationalSingularHomology 4 sphereProductTopCat ⟶ ModuleCat.of ℚ ℚ :=
  (SphereProductSingularChainComplex.homologyIsCokernel 5 4 (by simp)).desc
    (CokernelCofork.ofπ sphereProductFourReceiverOnCycles
      sphereProductFourReceiverOnCycles_boundaries)

@[reassoc] theorem homologyπ_sphereProductFourReceiverOnHomology :
    SphereProductSingularChainComplex.homologyπ 4 ≫ sphereProductFourReceiverOnHomology =
      sphereProductFourReceiverOnCycles := by
  simpa [sphereProductFourReceiverOnHomology] using
    (Cofork.IsColimit.π_desc (SphereProductSingularChainComplex.homologyIsCokernel 5 4 (by simp))
      (t := CokernelCofork.ofπ sphereProductFourReceiverOnCycles
        sphereProductFourReceiverOnCycles_boundaries))

theorem sphereProductFourReceiverOnHomology_fundamental :
    sphereProductFourReceiverOnHomology sphereProductFundamentalFourHomologyClass = 1 := by
  have included :
      SphereProductSingularChainComplex.iCycles 4
          (sphereProductFundamentalFourCycleLift 1) =
        sphereProductFundamentalFourChain := by
    change (sphereProductFundamentalFourCycleLift ≫
      SphereProductSingularChainComplex.iCycles 4) 1 = _
    rw [sphereProductFundamentalFourCycleLift_i]
    change (1 : ℚ) • sphereProductFundamentalFourChain = sphereProductFundamentalFourChain
    exact one_smul ℚ _
  have returned :
      sphereProductFourReceiverOnHomology
          (SphereProductSingularChainComplex.homologyπ 4
            (sphereProductFundamentalFourCycleLift 1)) =
        sphereProductFourReceiverOnCycles (sphereProductFundamentalFourCycleLift 1) := by
    change (SphereProductSingularChainComplex.homologyπ 4 ≫
      sphereProductFourReceiverOnHomology) (sphereProductFundamentalFourCycleLift 1) = _
    rw [homologyπ_sphereProductFourReceiverOnHomology]
  change sphereProductFourReceiverOnHomology
    (SphereProductSingularChainComplex.homologyπ 4
      (sphereProductFundamentalFourCycleLift 1)) = 1
  rw [returned]
  change sphereProductFourReceiver
    (SphereProductSingularChainComplex.iCycles 4 (sphereProductFundamentalFourCycleLift 1)) = 1
  rw [included]
  exact sphereProductFourReceiver_fundamental

theorem sphereProductFundamentalFourHomologyClass_ne_zero :
    sphereProductFundamentalFourHomologyClass ≠ 0 := by
  intro hzero
  have received := congrArg (fun x => sphereProductFourReceiverOnHomology x) hzero
  rw [sphereProductFourReceiverOnHomology_fundamental, map_zero] at received
  exact one_ne_zero received

section Audit

#print axioms sphereDetectorFromHomology
#print axioms sphereNormalizedCurrentCoefficient_return
#print axioms sphereNormalizedSimplexCoefficient_closed
#print axioms sphereNormalizedSimplexCoefficient_degenerate
#print axioms productChainDiagonalEquiv_boundary_five
#print axioms sphereProductFourReceiver_boundary
#print axioms sphereProductFourReceiver_fundamental
#print axioms sphereProductFundamentalFourChain_not_mem_boundary_range
#print axioms sphereProductFourReceiverOnHomology_fundamental
#print axioms sphereProductFundamentalFourHomologyClass_ne_zero

#print axioms topologicalProductSimplexEquiv
#print axioms topologicalProductSimplexRealization
#print axioms homeomorphicTopologicalProductSimplexEquiv
#print axioms homeomorphicTopologicalProductSimplexRealization
#print axioms topologicalSimplexMap_comp
#print axioms topologicalSimplexMap_id
#print axioms topologicalChainEquivCurrent
#print axioms topologicalChainEquivCurrent_boundary
#print axioms topologicalChainMap_simplexGenerator
#print axioms topologicalChainEquivCurrent_map
#print axioms productSimplexEquiv
#print axioms productChainEquivCurrent
#print axioms productChainDiagonalEquiv
#print axioms pairTwoBoundary_factor_incidence
#print axioms pairTwoShuffle_closed
#print axioms productChainDiagonalEquiv_boundary_four
#print axioms sphereProductFundamentalFourChain_closed
#print axioms productChainDiagonalEquiv_boundary_generator
#print axioms productChainDiagonalEquiv_boundary_three_generator
#print axioms productChainDiagonalEquiv_boundary
#print axioms productChainDiagonalEquiv_boundary_three
#print axioms separatedProductThreeChain_boundary
#print axioms productBoundarySeparationHolon
#print axioms separatedProductCycle_boundary
#print axioms productCycleSeparationHolon
#print axioms rejoinedProductThreeChain_boundary
#print axioms rejoinedProductChain_of_separatedBoundary
#print axioms productChainDiagonalEquiv_boundary_rejoined
#print axioms rejoinedProductChain_boundary
#print axioms rejoinedProductCycle
#print axioms productRoundTripDefectChain_diagonal
#print axioms productRoundTripDefectChain_boundary
#print axioms productRoundTripDefectCycle
#print axioms productRoundTripDefectFillerChain_boundary
#print axioms productReconstructionBoundaryHolon

end Audit

end Holonics.Hodge.HodgeProductDiagonal
