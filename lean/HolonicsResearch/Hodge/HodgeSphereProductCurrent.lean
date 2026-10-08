import HolonicsResearch.Hodge.HodgeTopologicalSingularCurrent

/-!
# The sphere-product singular-current chart

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

abbrev SphereSSet : SSet := TopCat.toSSet.obj sphereTopCat

abbrev ProductSSet : SSet := TopCat.toSSet.obj sphereProductTopCat

abbrev ProductSimplex (degree : ℕ) :=
  Simplex ProductSSet degree

abbrev ProductChain (degree : ℕ) :=
  SphereProductSingularChainComplex.X degree

abbrev ProductSimplicialModule : SimplicialObject (ModuleCat ℚ) :=
  ((SimplicialObject.whiskering Type (ModuleCat ℚ)).obj
    (sigmaConst.obj rationalCoefficient)).obj ProductSSet

def productSimplexFace {degree : ℕ} (omitted : Fin (degree + 2))
    (simplex : ProductSimplex (degree + 1)) : ProductSimplex degree :=
  ProductSSet.δ omitted simplex

/-- Coordinate projection of one genuine product simplex. -/
def splitProductSimplex {degree : ℕ} (simplex : ProductSimplex degree) :
    DiagonalOccurrence SphereSSet SphereSSet degree :=
  ((TopCat.toSSet.map firstProjectionTopMap).app
      (Opposite.op (SimplexCategory.mk degree)) simplex,
    (TopCat.toSSet.map secondProjectionTopMap).app
      (Opposite.op (SimplexCategory.mk degree)) simplex)

/-- Reconstruct a genuine product simplex from its two coordinate occurrences. -/
def joinProductSimplex {degree : ℕ}
    (pair : DiagonalOccurrence SphereSSet SphereSSet degree) : ProductSimplex degree :=
  (TopCat.toSSetObjEquiv sphereProductTopCat
    (Opposite.op (SimplexCategory.mk degree))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
          (Opposite.op (SimplexCategory.mk degree)) pair.1).prodMk
        (TopCat.toSSetObjEquiv sphereTopCat
          (Opposite.op (SimplexCategory.mk degree)) pair.2))

theorem split_join_productSimplex {degree : ℕ}
    (pair : DiagonalOccurrence SphereSSet SphereSSet degree) :
    splitProductSimplex (joinProductSimplex pair) = pair := by
  rcases pair with ⟨left, right⟩
  apply Prod.ext
  · apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk degree))).injective
    apply ContinuousMap.ext
    intro point
    rfl
  · apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk degree))).injective
    apply ContinuousMap.ext
    intro point
    rfl

theorem join_split_productSimplex {degree : ℕ} (simplex : ProductSimplex degree) :
    joinProductSimplex (splitProductSimplex simplex) = simplex := by
  apply (TopCat.toSSetObjEquiv sphereProductTopCat
    (Opposite.op (SimplexCategory.mk degree))).injective
  apply ContinuousMap.ext
  intro point
  apply Prod.ext <;> rfl

/-- [proved-derived; formal-checked] A genuine product simplex and its ordered coordinate pair
carry exactly the same occurrence, with both directions retained. -/
def productSimplexEquiv (degree : ℕ) :
    ProductSimplex degree ≃ DiagonalOccurrence SphereSSet SphereSSet degree where
  toFun := splitProductSimplex
  invFun := joinProductSimplex
  left_inv := join_split_productSimplex
  right_inv := split_join_productSimplex

theorem splitProductSimplex_face {degree : ℕ} (omitted : Fin (degree + 2))
    (simplex : ProductSimplex (degree + 1)) :
    splitProductSimplex (productSimplexFace omitted simplex) =
      diagonalFace omitted (splitProductSimplex simplex) := by
  apply Prod.ext
  · exact SSet.δ_naturality_apply (TopCat.toSSet.map firstProjectionTopMap)
      omitted simplex
  · exact SSet.δ_naturality_apply (TopCat.toSSet.map secondProjectionTopMap)
      omitted simplex

/-- The categorical singular generator for one genuine product simplex. -/
def productSimplexGenerator {degree : ℕ} (simplex : ProductSimplex degree) :
    ProductChain degree :=
  (Limits.Sigma.ι (fun _ : ProductSimplex degree => rationalCoefficient) simplex) (1 : ℚ)

theorem productSimplicialModule_face_generator {degree : ℕ}
    (omitted : Fin (degree + 2)) (simplex : ProductSimplex (degree + 1)) :
    (ProductSimplicialModule.δ omitted) (productSimplexGenerator simplex) =
      productSimplexGenerator (productSimplexFace omitted simplex) := by
  change (ModuleCat.Hom.hom (Limits.Sigma.map'
      (f := fun _ : ProductSimplex (degree + 1) => rationalCoefficient)
      (g := fun _ : ProductSimplex degree => rationalCoefficient)
      (ProductSSet.δ omitted)
      (fun _ => 𝟙 rationalCoefficient)))
      ((ModuleCat.Hom.hom
        (Limits.Sigma.ι (fun _ : ProductSimplex (degree + 1) => rationalCoefficient)
          simplex)) (1 : ℚ)) = _
  change ((Limits.Sigma.ι
      (fun _ : ProductSimplex (degree + 1) => rationalCoefficient) simplex ≫
      Limits.Sigma.map'
        (f := fun _ : ProductSimplex (degree + 1) => rationalCoefficient)
        (g := fun _ : ProductSimplex degree => rationalCoefficient)
        (ProductSSet.δ omitted)
        (fun _ => 𝟙 rationalCoefficient)) (1 : ℚ)) = _
  simp [productSimplexGenerator, productSimplexFace]

theorem boundary_productSimplexGenerator {degree : ℕ}
    (simplex : ProductSimplex (degree + 1)) :
    SphereProductSingularChainComplex.d (degree + 1) degree
        (productSimplexGenerator simplex) =
      ∑ omitted : Fin (degree + 2), (-1 : ℚ) ^ (omitted : ℕ) •
        productSimplexGenerator (productSimplexFace omitted simplex) := by
  dsimp only [SphereProductSingularChainComplex,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor, Functor.comp_obj]
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj ProductSimplicialModule).d
    (degree + 1) degree) (productSimplexGenerator simplex) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply,
    ModuleCat.hom_zsmul]
  have hsum :
      ((∑ omitted : Fin (degree + 2),
          ⇑(((-1 : ℤ) ^ (omitted : ℕ)) •
            ModuleCat.Hom.hom (ProductSimplicialModule.δ omitted)))
          (productSimplexGenerator simplex)) =
        ∑ omitted : Fin (degree + 2),
          (⇑(((-1 : ℤ) ^ (omitted : ℕ)) •
            ModuleCat.Hom.hom (ProductSimplicialModule.δ omitted)))
            (productSimplexGenerator simplex) := by
    simpa only [LinearMap.coe_sum] using
      (LinearMap.sum_apply (Finset.univ : Finset (Fin (degree + 2)))
        (fun omitted => ((-1 : ℤ) ^ (omitted : ℕ)) •
          ModuleCat.Hom.hom (ProductSimplicialModule.δ omitted))
        (productSimplexGenerator simplex))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro omitted _
  change ((-1 : ℤ) ^ (omitted : ℕ)) •
      (ProductSimplicialModule.δ omitted) (productSimplexGenerator simplex) =
    ((-1 : ℚ) ^ (omitted : ℕ)) •
      productSimplexGenerator (productSimplexFace omitted simplex)
  rw [productSimplicialModule_face_generator]
  have scalarLaw : ((-1 : ℚ) ^ (omitted : ℕ)) =
      (((-1 : ℤ) ^ (omitted : ℕ) : ℤ) : ℚ) := by
    norm_num
  rw [scalarLaw, Int.cast_smul_eq_zsmul]
  rfl

def productCurrentCoefficient {degree : ℕ} (simplex : ProductSimplex degree) :
    rationalCoefficient ⟶ ModuleCat.of ℚ (Current (ProductSimplex degree)) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ (generator simplex))

/-- Read the categorical coproduct as its complete finite occurrence current. -/
def chainToProductCurrentMorphism (degree : ℕ) :
    SphereProductSingularChainComplex.X degree ⟶
      ModuleCat.of ℚ (Current (ProductSimplex degree)) :=
  Limits.Sigma.desc fun simplex => productCurrentCoefficient simplex

def chainToProductCurrent (degree : ℕ) :
    ProductChain degree →ₗ[ℚ] Current (ProductSimplex degree) :=
  (chainToProductCurrentMorphism degree).hom

/-- Reconstruct the categorical singular chain from every retained finite occurrence. -/
def productCurrentToChain (degree : ℕ) :
    Current (ProductSimplex degree) →ₗ[ℚ] ProductChain degree :=
  Finsupp.linearCombination ℚ productSimplexGenerator

def productCurrentToChainMorphism (degree : ℕ) :
    ModuleCat.of ℚ (Current (ProductSimplex degree)) ⟶
      SphereProductSingularChainComplex.X degree :=
  ModuleCat.ofHom (productCurrentToChain degree)

@[simp]
theorem chainToProductCurrent_generator {degree : ℕ}
    (simplex : ProductSimplex degree) :
    chainToProductCurrent degree (productSimplexGenerator simplex) =
      generator simplex := by
  change ((Limits.Sigma.ι
      (fun _ : ProductSimplex degree => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => productCurrentCoefficient source)) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

@[simp]
theorem productCurrentToChain_generator {degree : ℕ}
    (simplex : ProductSimplex degree) :
    productCurrentToChain degree (generator simplex) = productSimplexGenerator simplex := by
  simp [productCurrentToChain, generator]

theorem sigmaInjection_eq_smul_productGenerator (degree : ℕ)
    (simplex : ProductSimplex degree) (coefficient : ℚ) :
    (Limits.Sigma.ι (fun _ : ProductSimplex degree => rationalCoefficient) simplex) coefficient =
      coefficient • productSimplexGenerator simplex := by
  let one : (rationalCoefficient : Type) := (1 : ℚ)
  let coefficientPoint : (rationalCoefficient : Type) := coefficient
  have hone : coefficient • one = coefficientPoint := by
    change coefficient * 1 = coefficient
    exact mul_one coefficient
  have hlinear := map_smul
    (Limits.Sigma.ι (fun _ : ProductSimplex degree => rationalCoefficient) simplex).hom
    coefficient one
  change (Limits.Sigma.ι (fun _ : ProductSimplex degree => rationalCoefficient) simplex)
      coefficientPoint = coefficient •
        (Limits.Sigma.ι (fun _ : ProductSimplex degree => rationalCoefficient) simplex) one
  rw [← hone]
  exact hlinear

theorem productCurrent_chain_roundtrip (degree : ℕ)
    (chain : ProductChain degree) :
    productCurrentToChain degree (chainToProductCurrent degree chain) = chain := by
  have composite_eq :
      chainToProductCurrentMorphism degree ≫ productCurrentToChainMorphism degree =
        𝟙 (SphereProductSingularChainComplex.X degree) := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    simp only [Category.assoc]
    change productCurrentToChain degree
        (chainToProductCurrent degree
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex degree => rationalCoefficient) simplex) coefficient)) =
      (Limits.Sigma.ι (fun _ : ProductSimplex degree => rationalCoefficient) simplex)
        coefficient
    rw [sigmaInjection_eq_smul_productGenerator]
    simp only [map_smul, chainToProductCurrent_generator,
      productCurrentToChain_generator]
  have pointLaw := congrArg (fun morphism => morphism chain) composite_eq
  exact pointLaw

theorem chain_productCurrent_roundtrip (degree : ℕ)
    (current : Current (ProductSimplex degree)) :
    chainToProductCurrent degree (productCurrentToChain degree current) = current := by
  let composite : Current (ProductSimplex degree) →ₗ[ℚ]
      Current (ProductSimplex degree) :=
    (chainToProductCurrent degree).comp (productCurrentToChain degree)
  have composite_eq : composite = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro simplex coefficient
    rw [show Finsupp.single simplex coefficient = coefficient • generator simplex by
      simp [generator]]
    simp only [composite, LinearMap.comp_apply, map_smul,
      productCurrentToChain_generator, chainToProductCurrent_generator,
      LinearMap.id_apply]
  exact LinearMap.congr_fun composite_eq current

/-- [proved-derived; formal-checked] The genuine rational singular-chain carrier is exactly the
free finite current of its product-simplex occurrences. -/
def productChainEquivCurrent (degree : ℕ) :
    ProductChain degree ≃ₗ[ℚ] Current (ProductSimplex degree) where
  toLinearMap := chainToProductCurrent degree
  invFun := productCurrentToChain degree
  left_inv := productCurrent_chain_roundtrip degree
  right_inv := chain_productCurrent_roundtrip degree

/-- [proved-derived; formal-checked] The genuine product chain is exactly the diagonal current of
its two coordinate singular simplices. -/
def productChainDiagonalEquiv (degree : ℕ) :
    ProductChain degree ≃ₗ[ℚ]
      Current (DiagonalOccurrence SphereSSet SphereSSet degree) :=
  (productChainEquivCurrent degree).trans
    (Finsupp.domLCongr (productSimplexEquiv degree))

def productChainDiagonalMorphism (degree : ℕ) :
    SphereProductSingularChainComplex.X degree ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet degree)) :=
  ModuleCat.ofHom (productChainDiagonalEquiv degree).toLinearMap

def separatedBoundaryAfterDiagonalMorphism :
    SphereProductSingularChainComplex.X 2 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 1)) :=
  ModuleCat.ofHom ((diagonalBoundaryTwo SphereSSet SphereSSet).comp
    (productChainDiagonalEquiv 2).toLinearMap)

@[simp]
theorem productChainDiagonalEquiv_generator {degree : ℕ}
    (simplex : ProductSimplex degree) :
    productChainDiagonalEquiv degree (productSimplexGenerator simplex) =
      generator (splitProductSimplex simplex) := by
  change (Finsupp.domLCongr (R := ℚ) (M := ℚ) (productSimplexEquiv degree))
      (chainToProductCurrent degree (productSimplexGenerator simplex)) = _
  rw [chainToProductCurrent_generator]
  simp [Finsupp.domLCongr_apply, Finsupp.domCongr_apply, generator,
    productSimplexEquiv]

section Audit

#print axioms split_join_productSimplex
#print axioms join_split_productSimplex
#print axioms splitProductSimplex_face
#print axioms productSimplicialModule_face_generator
#print axioms boundary_productSimplexGenerator
#print axioms chainToProductCurrent_generator
#print axioms productCurrentToChain_generator
#print axioms sigmaInjection_eq_smul_productGenerator
#print axioms productCurrent_chain_roundtrip
#print axioms chain_productCurrent_roundtrip
#print axioms productChainDiagonalEquiv_generator

end Audit

end Holonics.Hodge.HodgeProductDiagonal
