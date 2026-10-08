import HolonicsResearch.Hodge.HodgeProductRulingBoundary

/-!
# The public ruling homology consumer derives surjectivity and the equivalence from the actual boundary witness.

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

/-- [proved-derived; formal-checked] The geometric ruling map is onto genuine rational singular
homology.  Surjectivity is consumed from the source-level boundary witness above, not inferred from
a dimension count or a quotient-only interface. -/
theorem rulingHomologyMap_surjective :
    Function.Surjective rulingHomologyMap := by
  intro receivedClass
  obtain ⟨cycle, cycleClass⟩ :=
    (ModuleCat.epi_iff_surjective
      (ProductChains.homologyπ 2)).mp inferInstance receivedClass
  let sourceCycle : ProductTwoCycle :=
    ⟨ProductChains.iCycles 2 cycle, by
      change (ProductChains.iCycles 2 ≫ ProductChains.d 2 1) cycle = 0
      rw [ProductChains.iCycles_d]
      rfl⟩
  obtain ⟨coefficients, witness, boundary⟩ :=
    exists_productDegreeTwoRulingDecomposition sourceCycle
  let targetCycle : ProductChains.cycles 2 :=
    coefficients 0 •
        cycleLift firstRulingCycle firstRulingCycle_boundary_zero 1 +
      coefficients 1 •
        cycleLift secondRulingCycle secondRulingCycle_boundary_zero 1
  have targetInclusion :
      ProductChains.iCycles 2 targetCycle =
        coefficients 0 • firstRulingCycle +
          coefficients 1 • secondRulingCycle := by
    change ProductChains.iCycles 2
        (coefficients 0 •
            cycleLift firstRulingCycle firstRulingCycle_boundary_zero 1 +
          coefficients 1 •
            cycleLift secondRulingCycle secondRulingCycle_boundary_zero 1) = _
    rw [map_add, map_smul, map_smul]
    have firstLift := congrArg (fun morphism => morphism (1 : ℚ))
      (cycleLift_i firstRulingCycle firstRulingCycle_boundary_zero)
    have secondLift := congrArg (fun morphism => morphism (1 : ℚ))
      (cycleLift_i secondRulingCycle secondRulingCycle_boundary_zero)
    have firstInclusion :
        ProductChains.iCycles 2
            (cycleLift firstRulingCycle firstRulingCycle_boundary_zero 1) =
          firstRulingCycle := by
      change ProductChains.iCycles 2
          (cycleLift firstRulingCycle firstRulingCycle_boundary_zero 1) =
        chainElementMorphism firstRulingCycle 1 at firstLift
      exact firstLift.trans (by
        simpa using chainElementMorphism_apply firstRulingCycle 1)
    have secondInclusion :
        ProductChains.iCycles 2
            (cycleLift secondRulingCycle secondRulingCycle_boundary_zero 1) =
          secondRulingCycle := by
      change ProductChains.iCycles 2
          (cycleLift secondRulingCycle secondRulingCycle_boundary_zero 1) =
        chainElementMorphism secondRulingCycle 1 at secondLift
      exact secondLift.trans (by
        simpa using chainElementMorphism_apply secondRulingCycle 1)
    rw [firstInclusion, secondInclusion]
  have targetClass :
      ProductChains.homologyπ 2 targetCycle =
        rulingHomologyMap coefficients := by
    change ProductChains.homologyπ 2
        (coefficients 0 •
            cycleLift firstRulingCycle firstRulingCycle_boundary_zero 1 +
          coefficients 1 •
            cycleLift secondRulingCycle secondRulingCycle_boundary_zero 1) = _
    simp only [map_add, map_smul]
    rfl
  have differenceIsBoundary :
      cycle - targetCycle = ProductChains.toCycles 3 2 witness := by
    apply (ModuleCat.mono_iff_injective
      (ProductChains.iCycles 2)).mp inferInstance
    rw [map_sub, targetInclusion]
    change sourceCycle.1 -
        (coefficients 0 • firstRulingCycle +
          coefficients 1 • secondRulingCycle) =
      (ProductChains.toCycles 3 2 ≫ ProductChains.iCycles 2) witness
    rw [ProductChains.toCycles_i, boundary]
  have differenceVanishes :
      ProductChains.homologyπ 2 (cycle - targetCycle) = 0 := by
    rw [differenceIsBoundary]
    change (ProductChains.toCycles 3 2 ≫
      ProductChains.homologyπ 2) witness = 0
    rw [ProductChains.toCycles_comp_homologyπ]
    rfl
  have sameClass :
      ProductChains.homologyπ 2 cycle =
        ProductChains.homologyπ 2 targetCycle := by
    rw [map_sub, sub_eq_zero] at differenceVanishes
    exact differenceVanishes
  refine ⟨coefficients, ?_⟩
  exact targetClass.symm.trans (sameClass.symm.trans cycleClass)

/-- [proved-derived; formal-checked] The two geometric rulings give exact coordinates on genuine
degree-two rational singular homology of the sphere product.  Surjectivity is supplied by the
source-level coupled filling above; injectivity is the previously proved fundamental-class
obstruction. -/
def rulingHomologyEquivalence :
    Bidegree ≃ₗ[ℚ] RationalSingularHomology 2 sphereProductTopCat :=
  LinearEquiv.ofBijective rulingHomologyMap
    ⟨HodgeRefinedBoundaryObstruction.rulingHomologyMap_injective,
      rulingHomologyMap_surjective⟩

section Audit

#print axioms exists_productDegreeTwoRulingDecomposition
#print axioms rulingHomologyMap_surjective
#print axioms rulingHomologyEquivalence

end Audit

end Holonics.Hodge.HodgeProductRulingDecomposition
