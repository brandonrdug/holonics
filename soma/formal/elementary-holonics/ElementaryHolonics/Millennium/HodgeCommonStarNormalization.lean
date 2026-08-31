import ElementaryHolonics.Millennium.HodgeLabelWordContraction
import ElementaryHolonics.Millennium.HodgeLabelEdgeCancellation

/-!
# Exact common-star normalization

This file sums the fixed-chart ordered-word fillers over the complete refined common-star family.
The family boundary retains three distinct receivers: the raw affine-label current, the finite
tetrahedral face current, and the addressed edge-correction seam.  For a source cycle the seam
cancels through the already-owned refined boundary receiver.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Soma.Holonics.Millennium.HodgeCommonStarNormalization

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeIteratedBarycentricHomology
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeRefinedTriangleClosedStar
open Soma.Holonics.Millennium.HodgeRefinedTriangleAffineCarrier
open Soma.Holonics.Millennium.HodgeTriangleHomotopyPrism
open Soma.Holonics.Millennium.HodgeLabelEdgeCancellation
open Soma.Holonics.Millennium.HodgeLabelWordContraction

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- The complete coefficient-weighted family of local fixed-chart normalization fillers. -/
def refinedPrismNormalizationFiller {chain : SphereChain 2}
    {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 3 :=
  ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      rawAffineLabelSimplexNormalizationFiller
        (refinedCellLabels lebesgue family.labeling cell)

/-- [proved-derived; formal-checked] The summed filler returns the difference between the raw
affine-label family and its finite face receiver, retaining the complete correction seam. -/
theorem boundary_refinedPrismNormalizationFiller
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    SphereSingularChainComplex.d 3 2
        (refinedPrismNormalizationFiller family) =
      rawAffineLabelUpperCurrent family -
        faceRealization (refinedPrismUpperFaceCurrent family) -
          refinedFaceEdgeCorrectionCurrent family := by
  rw [refinedPrismNormalizationFiller, map_sum]
  simp only [map_smul]
  simp_rw [rawAffineLabelSimplexNormalizationFiller_boundary]
  rw [rawAffineLabelUpperCurrent, refinedPrismUpperFaceCurrent,
    refinedFaceEdgeCorrectionCurrent, map_sum]
  simp_rw [rawAffineLabelSimplexNormalizationDefect]
  simp only [map_smul, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  unfold refinedFaceEdgeCorrection refinedFaceLabels
  abel

/-- [proved-derived; formal-checked] For a source cycle the complete correction seam cancels, so
the family filler directly normalizes the raw affine current to its finite tetrahedral receiver. -/
theorem boundary_refinedPrismNormalizationFiller_of_cycle
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    SphereSingularChainComplex.d 3 2
        (refinedPrismNormalizationFiller family) =
      rawAffineLabelUpperCurrent family -
        faceRealization (refinedPrismUpperFaceCurrent family) := by
  rw [boundary_refinedPrismNormalizationFiller,
    refinedFaceEdgeCorrectionCurrent_eq_zero family cycle, sub_zero]

/-- The single current composing scale refinement, common-star transport, and fixed-chart
normalization. -/
def refinedCommonStarReductionCurrent {chain : SphereChain 2}
    {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 3 :=
  iteratedBarycentricDegreeTwoHomotopy family.scale chain +
    refinedPrismCurrent family - refinedPrismNormalizationFiller family

/-- [proved-derived; formal-checked] The composed current transports the original cycle directly
to the finite tetrahedral receiver.  Every intermediate raw and refined current cancels as an
actual shared boundary face. -/
theorem boundary_refinedCommonStarReductionCurrent
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    SphereSingularChainComplex.d 3 2
        (refinedCommonStarReductionCurrent family) =
      faceRealization (refinedPrismUpperFaceCurrent family) - chain := by
  rw [refinedCommonStarReductionCurrent, map_sub, map_add,
    boundary_iteratedBarycentricDegreeTwoHomotopy family.scale chain cycle,
    boundary_refinedPrismCurrent_of_cycle family cycle,
    boundary_refinedPrismNormalizationFiller_of_cycle family cycle,
    refinedPrismUpperCurrent_eq_rawAffineLabelUpperCurrent]
  module

/-- [proved-derived; formal-checked] The same reduction lands on the explicit one-dimensional
fundamental-cycle line of the tetrahedral sphere receiver. -/
theorem boundary_refinedCommonStarReductionCurrent_coordinates
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    SphereSingularChainComplex.d 3 2
        (refinedCommonStarReductionCurrent family) =
      refinedPrismUpperFaceCurrent family 0 • sphereFundamentalCandidate - chain := by
  rw [boundary_refinedCommonStarReductionCurrent family cycle,
    faceRealization_refinedPrismUpperFaceCurrent family cycle]

/-- [proved-derived; formal-checked] Every singular two-cycle on the sphere admits an explicit
finite-scale holonic transport to a rational multiple of the radial fundamental cycle. -/
theorem exists_commonStarReduction_to_fundamental
    (chain : SphereChain 2) (lebesgue : StarLebesgueLabel)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    ∃ current : SphereChain 3, ∃ coefficient : ℚ,
      SphereSingularChainComplex.d 3 2 current =
        coefficient • sphereFundamentalCandidate - chain := by
  obtain ⟨family⟩ := nonempty_refinedAffineCarrierFamily chain lebesgue
  exact ⟨refinedCommonStarReductionCurrent family,
    refinedPrismUpperFaceCurrent family 0,
    boundary_refinedCommonStarReductionCurrent_coordinates family cycle⟩

section Audit

#print axioms boundary_refinedPrismNormalizationFiller
#print axioms boundary_refinedPrismNormalizationFiller_of_cycle
#print axioms boundary_refinedCommonStarReductionCurrent
#print axioms boundary_refinedCommonStarReductionCurrent_coordinates
#print axioms exists_commonStarReduction_to_fundamental

end Audit

end Soma.Holonics.Millennium.HodgeCommonStarNormalization
