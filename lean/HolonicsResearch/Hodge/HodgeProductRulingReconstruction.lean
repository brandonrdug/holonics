import HolonicsResearch.Hodge.HodgeSphereRulingCurrent

/-!
# The separated outer currents rejoin to the existing geometric ruling chains exactly.

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

/-- [proved-derived; formal-checked] The first separated ruling is the exact `S² × point`
outer current. -/
theorem firstRulingSeparatedCurrent_eq :
    HodgeProductMixedFilling.firstRulingSeparatedCurrent =
      rightAxis
        (pairCurrent sphereFundamentalCurrent
          (generator rulingBasepointSimplex)) := by
  unfold HodgeProductMixedFilling.firstRulingSeparatedCurrent
    HodgeProductMixedFilling.secondRulingSeparatedCurrent
  rw [pairFirstBase_current, totalTwoFlip_leftAxis,
    flipPair_pairCurrent]

/-- [proved-derived; formal-checked] Rejoining one `2 × 0` outer current repeats the retained
basepoint into the diagonal degree-two chart. -/
theorem rejoinTwo_rightAxis_base
    (current : Current (SphereSimplex 2)) :
    rejoinTwo HodgeProductDiagonal.SphereSSet HodgeProductDiagonal.SphereSSet
        (rightAxis
          (pairCurrent current (generator rulingBasepointSimplex))) =
      pairCurrent current
        (generator (repeatVertexTriangle rulingBasepointSimplex)) := by
  induction current using Finsupp.induction_linear with
  | zero => simp [pairCurrent]
  | add left right hleft hright =>
      simp only [pairCurrent_add_left, map_add, hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [pairCurrent_smul_left, map_smul, pairCurrent_generator,
        rightAxis_generator, rejoinTwo, extend_generator, rejoinTwoAtom]

/-- [proved-derived; formal-checked] Rejoining the opposite outer current is the same operation
in the reversed presentation. -/
theorem rejoinTwo_leftAxis_base
    (current : Current (SphereSimplex 2)) :
    rejoinTwo HodgeProductDiagonal.SphereSSet HodgeProductDiagonal.SphereSSet
        (leftAxis
          (pairCurrent (generator rulingBasepointSimplex) current)) =
      pairCurrent
        (generator (repeatVertexTriangle rulingBasepointSimplex)) current := by
  induction current using Finsupp.induction_linear with
  | zero => simp [pairCurrent]
  | add left right hleft hright =>
      simp only [pairCurrent_add_right, map_add, hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [pairCurrent_smul_right, map_smul, pairCurrent_generator,
        leftAxis_generator, rejoinTwo, extend_generator, rejoinTwoAtom]

/-- [proved-derived; formal-checked] The rejoined first basis current is its complete diagonal
occurrence population. -/
theorem rejoinTwo_firstRulingSeparatedCurrent :
    rejoinTwo HodgeProductDiagonal.SphereSSet HodgeProductDiagonal.SphereSSet
        HodgeProductMixedFilling.firstRulingSeparatedCurrent =
      pairCurrent sphereFundamentalCurrent
        (generator (repeatVertexTriangle rulingBasepointSimplex)) := by
  rw [firstRulingSeparatedCurrent_eq, rejoinTwo_rightAxis_base]

/-- [proved-derived; formal-checked] The rejoined second basis current is the reversed complete
diagonal occurrence population. -/
theorem rejoinTwo_secondRulingSeparatedCurrent :
    rejoinTwo HodgeProductDiagonal.SphereSSet HodgeProductDiagonal.SphereSSet
        HodgeProductMixedFilling.secondRulingSeparatedCurrent =
      pairCurrent (generator (repeatVertexTriangle rulingBasepointSimplex))
        sphereFundamentalCurrent := by
  rw [HodgeProductMixedFilling.secondRulingSeparatedCurrent, pairFirstBase_current,
    rejoinTwo_leftAxis_base]

/-- [proved-derived; formal-checked] The first separated basis rejoins to the repository's
geometric first ruling cycle exactly, not merely to its homology class. -/
theorem rejoinedProductChain_firstRulingSeparatedCurrent :
    rejoinedProductChain
        HodgeProductMixedFilling.firstRulingSeparatedCurrent =
      firstRulingCycle := by
  apply (productChainDiagonalEquiv 2).injective
  rw [rejoinedProductChain, LinearEquiv.apply_symm_apply,
    rejoinTwo_firstRulingSeparatedCurrent,
    productChainDiagonalEquiv_firstRulingCycle]

/-- [proved-derived; formal-checked] The opposite separated basis rejoins to the geometric
second ruling cycle exactly. -/
theorem rejoinedProductChain_secondRulingSeparatedCurrent :
    rejoinedProductChain
        HodgeProductMixedFilling.secondRulingSeparatedCurrent =
      secondRulingCycle := by
  apply (productChainDiagonalEquiv 2).injective
  rw [rejoinedProductChain, LinearEquiv.apply_symm_apply,
    rejoinTwo_secondRulingSeparatedCurrent,
    productChainDiagonalEquiv_secondRulingCycle]

section Audit

#print axioms firstRulingSeparatedCurrent_eq
#print axioms rejoinTwo_rightAxis_base
#print axioms rejoinTwo_leftAxis_base
#print axioms rejoinTwo_firstRulingSeparatedCurrent
#print axioms rejoinTwo_secondRulingSeparatedCurrent
#print axioms rejoinedProductChain_firstRulingSeparatedCurrent
#print axioms rejoinedProductChain_secondRulingSeparatedCurrent

end Audit

end Holonics.Hodge.HodgeProductRulingDecomposition
