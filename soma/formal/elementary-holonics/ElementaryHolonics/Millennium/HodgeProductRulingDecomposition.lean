import ElementaryHolonics.Millennium.HodgeProductMixedFilling
import ElementaryHolonics.Millennium.HodgeRefinedBoundaryObstruction

/-!
# Exact source-level ruling decomposition on the sphere product

This file consumes the coupled separated-current reduction and returns to the genuine singular
chain receiver.  Its only chart obligation is to identify the two graded outer currents with the
already constructed geometric ruling cycles.  No quotient-only homology assertion substitutes for
the degree-three boundary witness.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProductRulingDecomposition

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Soma.Holonics.DiagonalChainTransport hiding
  correctedFirstOuter correctedFirstOuter_closed correctedSecondOuter correctedSecondOuter_closed
  coupledAxisBoundaryEquations coupledMiddleCorrection coupledMiddleCorrection_boundary
  coupledMiddleCorrection_reduces_to_outer leftAxis leftAxis_generator leftAxisProjection
  leftMiddleAxis
  leftOneAxisProjection leftOneAxisProjection_totalBoundaryTwo leftOuterBoundary mapPairLeft
  mapPairLeft_comp mapPairLeft_generator mapPairLeft_pairCurrent mapPairLeft_right_commute
  mapPairRight mapPairRight_comp mapPairRight_generator mapPairRight_pairCurrent middleAxis
  middleAxisProjection middleFirstBoundary middleSecondBoundary
  mixedFirstBoundary_closed_of_totalBoundary mixedSecondBoundary_closed_of_totalBoundary
  pairCurrent pairCurrent_add_left pairCurrent_add_right pairCurrent_generator
  pairCurrent_neg_left pairCurrent_neg_right pairCurrent_smul_left pairCurrent_smul_right
  pairCurrent_sub_right pairCurrent_zero_right pairFirstAugmentation
  pairFirstAugmentation_mapPairLeft_boundary pairFirstAugmentation_mapPairRight
  pairFirstAugmentation_pairCurrent pairFirstBase pairFirstBase_current rightAxis
  rightAxis_generator rightAxisProjection rightMiddleAxis rightOneAxisProjection
  rightOneAxisProjection_totalBoundaryTwo rightOuterBoundary
  totalBoundaryThree_leftMiddleAxis totalBoundaryThree_rightMiddleAxis
  totalTwoAxisReconstruction
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeSphereProductRulingCycles
open Soma.Holonics.Millennium.HodgeSphereProductRulingHomology
open Soma.Holonics.Millennium.HodgeProductDiagonal
open Soma.Holonics.Millennium.HodgeSphereChainCurrent
open Soma.Holonics.Millennium.HodgeProductMixedFilling

/-- The product singular simplex obtained by the simplicial image of a sphere simplex. -/
def sphereToProductSimplex {degree : ℕ}
    (map : sphereTopCat ⟶ sphereProductTopCat)
    (simplex : SphereSimplex degree) : ProductSimplex degree :=
  (TopCat.toSSet.map map).app
    (Opposite.op (SimplexCategory.mk degree)) simplex

/-- [proved-derived; formal-checked] A continuous sphere-to-product map sends one categorical
singular generator to the generator of its exact simplicial image. -/
theorem sphereToProductChainMap_generator {degree : ℕ}
    (map : sphereTopCat ⟶ sphereProductTopCat)
    (simplex : SphereSimplex degree) :
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map map).f degree (simplexGenerator simplex) =
      productSimplexGenerator (sphereToProductSimplex map simplex) := by
  change (ModuleCat.Hom.hom (Limits.Sigma.map'
      (f := fun _ : SphereSimplex degree => rationalCoefficient)
      (g := fun _ : ProductSimplex degree => rationalCoefficient)
      ((TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)))
      (fun _ => 𝟙 rationalCoefficient)))
      ((ModuleCat.Hom.hom
        (Limits.Sigma.ι (fun _ : SphereSimplex degree => rationalCoefficient)
          simplex)) (1 : ℚ)) = _
  have inclusion := Limits.Sigma.ι_comp_map'
    (f := fun _ : SphereSimplex degree => rationalCoefficient)
    (g := fun _ : ProductSimplex degree => rationalCoefficient)
    ((TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)))
    (fun _ : SphereSimplex degree => 𝟙 rationalCoefficient) simplex
  exact congrArg (fun morphism => (ModuleCat.Hom.hom morphism) (1 : ℚ)) inclusion

/-- [proved-derived; formal-checked] The first ruling simplex splits into the original sphere
simplex and the repeated ruling basepoint. -/
theorem split_firstRuling_simplex (simplex : SphereSimplex 2) :
    splitProductSimplex
        (sphereToProductSimplex firstRulingTopMap simplex) =
      (simplex, repeatVertexTriangle rulingBasepointSimplex) := by
  apply Prod.ext
  · apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2))).injective
    apply ContinuousMap.ext
    intro point
    rfl
  · apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2))).injective
    apply ContinuousMap.ext
    intro point
    rfl

/-- [proved-derived; formal-checked] The second ruling simplex has the opposite exact split. -/
theorem split_secondRuling_simplex (simplex : SphereSimplex 2) :
    splitProductSimplex
        (sphereToProductSimplex secondRulingTopMap simplex) =
      (repeatVertexTriangle rulingBasepointSimplex, simplex) := by
  apply Prod.ext
  · apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2))).injective
    apply ContinuousMap.ext
    intro point
    rfl
  · apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2))).injective
    apply ContinuousMap.ext
    intro point
    rfl

/-- [proved-derived; formal-checked] One first-ruling generator becomes the exact repeated-point
diagonal occurrence. -/
theorem productChainDiagonalEquiv_firstRuling_generator
    (simplex : SphereSimplex 2) :
    productChainDiagonalEquiv 2
        (firstRulingChainMap.f 2 (simplexGenerator simplex)) =
      generator (simplex, repeatVertexTriangle rulingBasepointSimplex) := by
  rw [firstRulingChainMap,
    sphereToProductChainMap_generator,
    productChainDiagonalEquiv_generator,
    split_firstRuling_simplex]

/-- [proved-derived; formal-checked] One second-ruling generator has the reversed exact
diagonal occurrence. -/
theorem productChainDiagonalEquiv_secondRuling_generator
    (simplex : SphereSimplex 2) :
    productChainDiagonalEquiv 2
        (secondRulingChainMap.f 2 (simplexGenerator simplex)) =
      generator (repeatVertexTriangle rulingBasepointSimplex, simplex) := by
  rw [secondRulingChainMap,
    sphereToProductChainMap_generator,
    productChainDiagonalEquiv_generator,
    split_secondRuling_simplex]

/-- Pairing distributes over every finite presented population in its first incidence. -/
theorem pairCurrent_univ_sum_left {Index Left Right : Type*}
    [Fintype Index] [DecidableEq Index]
    (family : Index → Current Left) (right : Current Right) :
    pairCurrent (∑ index, family index) right =
      ∑ index, pairCurrent (family index) right := by
  classical
  let pairing : Current Left →ₗ[ℚ] Current (Left × Right) :=
    { toFun := fun left => pairCurrent left right
      map_add' := fun left₁ left₂ => pairCurrent_add_left left₁ left₂ right
      map_smul' := fun coefficient left =>
        pairCurrent_smul_left coefficient left right }
  change pairing (∑ index, family index) =
    ∑ index, pairing (family index)
  rw [map_sum]

/-- Pairing distributes over every finite presented population in its second incidence. -/
theorem pairCurrent_univ_sum_right {Index Left Right : Type*}
    [Fintype Index] [DecidableEq Index]
    (left : Current Left) (family : Index → Current Right) :
    pairCurrent left (∑ index, family index) =
      ∑ index, pairCurrent left (family index) := by
  classical
  let pairing : Current Right →ₗ[ℚ] Current (Left × Right) :=
    { toFun := fun right => pairCurrent left right
      map_add' := fun right₁ right₂ => pairCurrent_add_right left right₁ right₂
      map_smul' := fun coefficient right =>
        pairCurrent_smul_right coefficient left right }
  change pairing (∑ index, family index) =
    ∑ index, pairing (family index)
  rw [map_sum]

/-- [proved-derived; formal-checked] The genuine first ruling cycle has exactly the same complete
diagonal occurrence current as the rejoined first separated basis. -/
theorem productChainDiagonalEquiv_firstRulingCycle :
    productChainDiagonalEquiv 2 firstRulingCycle =
      pairCurrent sphereFundamentalCurrent
        (generator (repeatVertexTriangle rulingBasepointSimplex)) := by
  rw [firstRulingCycle, sphereFundamentalCandidate, map_sum]
  rw [map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_firstRuling_generator]
  rw [sphereFundamentalCurrent, sphereFundamentalCandidate, map_sum,
    pairCurrent_univ_sum_left]
  simp_rw [map_smul, sphereChainToCurrent_simplexGenerator,
    pairCurrent_smul_left, pairCurrent_generator]

/-- [proved-derived; formal-checked] The genuine second ruling cycle has the reversed exact
diagonal occurrence current. -/
theorem productChainDiagonalEquiv_secondRulingCycle :
    productChainDiagonalEquiv 2 secondRulingCycle =
      pairCurrent (generator (repeatVertexTriangle rulingBasepointSimplex))
        sphereFundamentalCurrent := by
  rw [secondRulingCycle, sphereFundamentalCandidate, map_sum]
  rw [map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_secondRuling_generator]
  rw [sphereFundamentalCurrent, sphereFundamentalCandidate, map_sum,
    pairCurrent_univ_sum_right]
  simp_rw [map_smul, sphereChainToCurrent_simplexGenerator,
    pairCurrent_smul_right, pairCurrent_generator]

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

end Soma.Holonics.Millennium.HodgeProductRulingDecomposition
