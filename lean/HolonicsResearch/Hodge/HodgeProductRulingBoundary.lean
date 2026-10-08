import HolonicsResearch.Hodge.HodgeProductRulingReconstruction

/-!
# The coupled filling and reconstruction defect return an actual singular three-boundary witness.

[agent-inferred] This complete owner contains existing declarations moved once from
HodgeProductRulingDecomposition. Statements, proof bodies, namespace and local
scope are preserved. Its next owner consumes these laws; kernel acceptance
requires the whole maintained module and never follows from a partial read.
-/

noncomputable section

namespace Holonics.Hodge.HodgeProductRulingDecomposition

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Holonics.DiagonalChainTransport hiding
  correctedFirstOuter correctedFirstOuter_closed correctedSecondOuter correctedSecondOuter_closed
  coupledAxisBoundaryEquations coupledMiddleCorrection coupledMiddleCorrection_boundary
  coupledMiddleCorrection_reduces_to_outer leftAxis leftAxis_generator leftAxisProjection
  leftMiddleAxis leftOneAxisProjection leftOneAxisProjection_totalBoundaryTwo leftOuterBoundary
  middleAxis middleAxisProjection middleFirstBoundary middleSecondBoundary
  mixedFirstBoundary_closed_of_totalBoundary mixedSecondBoundary_closed_of_totalBoundary
  pairFirstAugmentation pairFirstAugmentation_mapPairLeft_boundary
  pairFirstAugmentation_mapPairRight pairFirstAugmentation_pairCurrent pairFirstBase
  pairFirstBase_current rightAxis rightAxis_generator rightAxisProjection rightMiddleAxis
  rightOneAxisProjection rightOneAxisProjection_totalBoundaryTwo rightOuterBoundary
  totalBoundaryThree_leftMiddleAxis totalBoundaryThree_rightMiddleAxis totalTwoAxisReconstruction
open Holonics.Hodge.HodgeProjectiveLineProduct
open Holonics.Hodge.HodgeProjectiveLineSingularReduction
open Holonics.Hodge.HodgeTwoSphereFundamentalCycle
open Holonics.Hodge.HodgeSphereProductRulingCycles
open Holonics.Hodge.HodgeSphereProductRulingHomology
open Holonics.Hodge.HodgeProductDiagonal
open Holonics.Hodge.HodgeSphereChainCurrent
open Holonics.Hodge.HodgeProductMixedFilling

/-- [proved-derived; formal-checked] Every genuine rational singular two-cycle on `S² × S²`
is the sum of the two geometric ruling cycles plus the boundary of an actual singular three-chain.
This is the frozen source-level Hodge validation gate; the complete reconstruction witness is part
of the return. -/
theorem exists_productDegreeTwoRulingDecomposition
    (cycle : ProductTwoCycle) :
    ∃ coefficients : Bidegree, ∃ witness : ProductChain 3,
      HodgeSphereProductFiniteComplex.SphereProductSingularChainComplex.d 3 2 witness =
        cycle.1 -
          (coefficients 0 • firstRulingCycle +
            coefficients 1 • secondRulingCycle) := by
  obtain ⟨coefficients, separatedFilling, separatedBoundary⟩ :=
    exists_closedTotalRulingReduction
      (separatedProductCycle cycle)
      (separatedProductCycle_boundary cycle)
  refine ⟨coefficients,
    rejoinedProductThreeChain separatedFilling -
      productRoundTripDefectFillerChain cycle, ?_⟩
  rw [map_sub, rejoinedProductThreeChain_boundary,
    productRoundTripDefectFillerChain_boundary,
    separatedBoundary]
  have rejoinedSub :
      rejoinedProductChain
          (separatedProductCycle cycle -
            (coefficients 0 •
                HodgeProductMixedFilling.firstRulingSeparatedCurrent +
              coefficients 1 •
                HodgeProductMixedFilling.secondRulingSeparatedCurrent)) =
        rejoinedProductChain (separatedProductCycle cycle) -
          rejoinedProductChain
            (coefficients 0 •
                HodgeProductMixedFilling.firstRulingSeparatedCurrent +
              coefficients 1 •
                HodgeProductMixedFilling.secondRulingSeparatedCurrent) := by
    simp [rejoinedProductChain]
  rw [rejoinedSub]
  have rejoinedCombination :
      rejoinedProductChain
          (coefficients 0 •
              HodgeProductMixedFilling.firstRulingSeparatedCurrent +
            coefficients 1 •
              HodgeProductMixedFilling.secondRulingSeparatedCurrent) =
        coefficients 0 •
            rejoinedProductChain
              HodgeProductMixedFilling.firstRulingSeparatedCurrent +
          coefficients 1 •
            rejoinedProductChain
              HodgeProductMixedFilling.secondRulingSeparatedCurrent := by
    simp [rejoinedProductChain]
  rw [rejoinedCombination,
    rejoinedProductChain_firstRulingSeparatedCurrent,
    rejoinedProductChain_secondRulingSeparatedCurrent]
  have defectLaw :
      productRoundTripDefectChain cycle.1 =
        rejoinedProductChain (separatedProductCycle cycle) - cycle.1 := by
    rfl
  rw [defectLaw]
  module

section Audit

#print axioms exists_productDegreeTwoRulingDecomposition

end Audit

end Holonics.Hodge.HodgeProductRulingDecomposition
