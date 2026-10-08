import HolonicsResearch.Hodge.HodgeProductMixedFilling
import HolonicsResearch.Hodge.HodgeRefinedBoundaryObstruction

/-!
# The actual sphere-to-product simplex map and the complete geometric ruling current chart.

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

section Audit

#print axioms sphereToProductSimplex
#print axioms sphereToProductChainMap_generator
#print axioms split_firstRuling_simplex
#print axioms split_secondRuling_simplex
#print axioms productChainDiagonalEquiv_firstRuling_generator
#print axioms productChainDiagonalEquiv_secondRuling_generator
#print axioms pairCurrent_univ_sum_left
#print axioms pairCurrent_univ_sum_right
#print axioms productChainDiagonalEquiv_firstRulingCycle
#print axioms productChainDiagonalEquiv_secondRulingCycle

end Audit

end Holonics.Hodge.HodgeProductRulingDecomposition
