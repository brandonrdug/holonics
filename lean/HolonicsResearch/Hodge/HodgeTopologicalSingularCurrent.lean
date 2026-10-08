import HolonicsResearch.Hodge.HodgeTopologicalProductRealization

/-!
# The generic rational singular-current chart

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

/-! ## One chain/current chart for every topological source

The singular-chain coproduct and the finitely supported addressed-simplex current are not two
carriers.  They are two receiver charts on the same occurrence population.  Keeping this adapter
generic prevents every new source (sphere, sphere power, or product) from acquiring another copy
of the same conversion proof.
-/

abbrev topologicalSingularChainComplex (Z : TopCat) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).obj Z

abbrev topologicalSimplex (Z : TopCat) (degree : ℕ) :=
  Simplex (topologicalFactorSSet Z) degree

abbrev topologicalChain (Z : TopCat) (degree : ℕ) :=
  (topologicalSingularChainComplex Z).X degree

abbrev topologicalSimplicialModule (Z : TopCat) :
    SimplicialObject (ModuleCat ℚ) :=
  ((SimplicialObject.whiskering Type (ModuleCat ℚ)).obj
    (sigmaConst.obj rationalCoefficient)).obj (topologicalFactorSSet Z)

/-- The categorical generator retaining one addressed simplex occurrence. -/
def topologicalSimplexGenerator (Z : TopCat) {degree : ℕ}
    (simplex : topologicalSimplex Z degree) : topologicalChain Z degree :=
  (Limits.Sigma.ι
    (fun _ : topologicalSimplex Z degree => rationalCoefficient) simplex) (1 : ℚ)

def topologicalSimplexFace (Z : TopCat) {degree : ℕ}
    (omitted : Fin (degree + 2))
    (simplex : topologicalSimplex Z (degree + 1)) : topologicalSimplex Z degree :=
  (topologicalFactorSSet Z).δ omitted simplex

theorem topologicalSimplicialModule_face_generator (Z : TopCat) {degree : ℕ}
    (omitted : Fin (degree + 2))
    (simplex : topologicalSimplex Z (degree + 1)) :
    (topologicalSimplicialModule Z).δ omitted
        (topologicalSimplexGenerator Z simplex) =
      topologicalSimplexGenerator Z (topologicalSimplexFace Z omitted simplex) := by
  change (ModuleCat.Hom.hom (Limits.Sigma.map'
      (f := fun _ : topologicalSimplex Z (degree + 1) => rationalCoefficient)
      (g := fun _ : topologicalSimplex Z degree => rationalCoefficient)
      ((topologicalFactorSSet Z).δ omitted)
      (fun _ => 𝟙 rationalCoefficient)))
      ((ModuleCat.Hom.hom
        (Limits.Sigma.ι
          (fun _ : topologicalSimplex Z (degree + 1) => rationalCoefficient)
          simplex)) (1 : ℚ)) = _
  change ((Limits.Sigma.ι
      (fun _ : topologicalSimplex Z (degree + 1) => rationalCoefficient) simplex ≫
      Limits.Sigma.map'
        (f := fun _ : topologicalSimplex Z (degree + 1) => rationalCoefficient)
        (g := fun _ : topologicalSimplex Z degree => rationalCoefficient)
        ((topologicalFactorSSet Z).δ omitted)
        (fun _ => 𝟙 rationalCoefficient)) (1 : ℚ)) = _
  simp [topologicalSimplexGenerator, topologicalSimplexFace]

/-- The genuine singular boundary on one generic addressed generator. -/
theorem boundary_topologicalSimplexGenerator (Z : TopCat) {degree : ℕ}
    (simplex : topologicalSimplex Z (degree + 1)) :
    (topologicalSingularChainComplex Z).d (degree + 1) degree
        (topologicalSimplexGenerator Z simplex) =
      ∑ omitted : Fin (degree + 2), (-1 : ℚ) ^ (omitted : ℕ) •
        topologicalSimplexGenerator Z (topologicalSimplexFace Z omitted simplex) := by
  dsimp only [topologicalSingularChainComplex,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor, Functor.comp_obj]
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
    (topologicalSimplicialModule Z)).d (degree + 1) degree)
      (topologicalSimplexGenerator Z simplex) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply,
    ModuleCat.hom_zsmul]
  have hsum :
      ((∑ omitted : Fin (degree + 2),
          ⇑(((-1 : ℤ) ^ (omitted : ℕ)) •
            ModuleCat.Hom.hom ((topologicalSimplicialModule Z).δ omitted)))
          (topologicalSimplexGenerator Z simplex)) =
        ∑ omitted : Fin (degree + 2),
          (⇑(((-1 : ℤ) ^ (omitted : ℕ)) •
            ModuleCat.Hom.hom ((topologicalSimplicialModule Z).δ omitted)))
            (topologicalSimplexGenerator Z simplex) := by
    simpa only [LinearMap.coe_sum] using
      (LinearMap.sum_apply (Finset.univ : Finset (Fin (degree + 2)))
        (fun omitted => ((-1 : ℤ) ^ (omitted : ℕ)) •
          ModuleCat.Hom.hom ((topologicalSimplicialModule Z).δ omitted))
        (topologicalSimplexGenerator Z simplex))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro omitted _
  change ((-1 : ℤ) ^ (omitted : ℕ)) •
      (topologicalSimplicialModule Z).δ omitted
        (topologicalSimplexGenerator Z simplex) =
    ((-1 : ℚ) ^ (omitted : ℕ)) •
      topologicalSimplexGenerator Z (topologicalSimplexFace Z omitted simplex)
  rw [topologicalSimplicialModule_face_generator]
  have scalarLaw : ((-1 : ℚ) ^ (omitted : ℕ)) =
      (((-1 : ℤ) ^ (omitted : ℕ) : ℤ) : ℚ) := by
    norm_num
  rw [scalarLaw, Int.cast_smul_eq_zsmul]
  rfl

def topologicalCurrentCoefficient (Z : TopCat) {degree : ℕ}
    (simplex : topologicalSimplex Z degree) :
    rationalCoefficient ⟶
      ModuleCat.of ℚ (FactorCurrent (topologicalFactorSSet Z) degree) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ (generator simplex))

/-- Read a categorical singular chain as its complete addressed occurrence current. -/
def topologicalChainToCurrentMorphism (Z : TopCat) (degree : ℕ) :
    (topologicalSingularChainComplex Z).X degree ⟶
      ModuleCat.of ℚ (FactorCurrent (topologicalFactorSSet Z) degree) :=
  Limits.Sigma.desc fun simplex => topologicalCurrentCoefficient Z simplex

def topologicalChainToCurrent (Z : TopCat) (degree : ℕ) :
    topologicalChain Z degree →ₗ[ℚ]
      FactorCurrent (topologicalFactorSSet Z) degree :=
  (topologicalChainToCurrentMorphism Z degree).hom

/-- Reconstruct the categorical chain from every retained addressed occurrence. -/
def topologicalCurrentToChain (Z : TopCat) (degree : ℕ) :
    FactorCurrent (topologicalFactorSSet Z) degree →ₗ[ℚ]
      topologicalChain Z degree :=
  Finsupp.linearCombination ℚ (topologicalSimplexGenerator Z)

@[simp]
theorem topologicalChainToCurrent_generator (Z : TopCat) {degree : ℕ}
    (simplex : topologicalSimplex Z degree) :
    topologicalChainToCurrent Z degree (topologicalSimplexGenerator Z simplex) =
      generator simplex := by
  change ((Limits.Sigma.ι
      (fun _ : topologicalSimplex Z degree => rationalCoefficient) simplex ≫
        Limits.Sigma.desc
          (fun source => topologicalCurrentCoefficient Z source)) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

@[simp]
theorem topologicalCurrentToChain_generator (Z : TopCat) {degree : ℕ}
    (simplex : topologicalSimplex Z degree) :
    topologicalCurrentToChain Z degree (generator simplex) =
      topologicalSimplexGenerator Z simplex := by
  simp [topologicalCurrentToChain, generator]

theorem sigmaInjection_eq_smul_topologicalSimplexGenerator (Z : TopCat)
    (degree : ℕ) (simplex : topologicalSimplex Z degree) (coefficient : ℚ) :
    (Limits.Sigma.ι
      (fun _ : topologicalSimplex Z degree => rationalCoefficient) simplex) coefficient =
      coefficient • topologicalSimplexGenerator Z simplex := by
  let one : (rationalCoefficient : Type) := (1 : ℚ)
  let coefficientPoint : (rationalCoefficient : Type) := coefficient
  have hone : coefficient • one = coefficientPoint := by
    change coefficient * 1 = coefficient
    exact mul_one coefficient
  have hlinear := map_smul
    (Limits.Sigma.ι
      (fun _ : topologicalSimplex Z degree => rationalCoefficient) simplex).hom
    coefficient one
  change (Limits.Sigma.ι
      (fun _ : topologicalSimplex Z degree => rationalCoefficient) simplex)
      coefficientPoint = coefficient •
        (Limits.Sigma.ι
          (fun _ : topologicalSimplex Z degree => rationalCoefficient) simplex) one
  rw [← hone]
  exact hlinear

theorem topologicalCurrent_chain_roundtrip (Z : TopCat) (degree : ℕ)
    (chain : topologicalChain Z degree) :
    topologicalCurrentToChain Z degree
        (topologicalChainToCurrent Z degree chain) = chain := by
  have composite_eq :
      topologicalChainToCurrentMorphism Z degree ≫
          ModuleCat.ofHom (topologicalCurrentToChain Z degree) =
        𝟙 ((topologicalSingularChainComplex Z).X degree) := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change topologicalCurrentToChain Z degree
        (topologicalChainToCurrent Z degree
          ((Limits.Sigma.ι
            (fun _ : topologicalSimplex Z degree => rationalCoefficient)
            simplex) coefficient)) =
      (Limits.Sigma.ι
        (fun _ : topologicalSimplex Z degree => rationalCoefficient)
        simplex) coefficient
    rw [sigmaInjection_eq_smul_topologicalSimplexGenerator]
    simp only [map_smul, topologicalChainToCurrent_generator,
      topologicalCurrentToChain_generator]
  exact congrArg (fun morphism => morphism chain) composite_eq

theorem topologicalChain_current_roundtrip (Z : TopCat) (degree : ℕ)
    (current : FactorCurrent (topologicalFactorSSet Z) degree) :
    topologicalChainToCurrent Z degree
        (topologicalCurrentToChain Z degree current) = current := by
  let composite : FactorCurrent (topologicalFactorSSet Z) degree →ₗ[ℚ]
      FactorCurrent (topologicalFactorSSet Z) degree :=
    (topologicalChainToCurrent Z degree).comp
      (topologicalCurrentToChain Z degree)
  have composite_eq : composite = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro simplex coefficient
    rw [show Finsupp.single simplex coefficient = coefficient • generator simplex by
      simp [generator]]
    simp only [composite, LinearMap.comp_apply, map_smul,
      topologicalCurrentToChain_generator, topologicalChainToCurrent_generator,
      LinearMap.id_apply]
  exact LinearMap.congr_fun composite_eq current

/-- [proved-derived; formal-checked] For every topological source, the actual rational singular
chain and its complete addressed occurrence population are the same linear carrier. -/
def topologicalChainEquivCurrent (Z : TopCat) (degree : ℕ) :
    topologicalChain Z degree ≃ₗ[ℚ]
      FactorCurrent (topologicalFactorSSet Z) degree where
  toLinearMap := topologicalChainToCurrent Z degree
  invFun := topologicalCurrentToChain Z degree
  left_inv := topologicalCurrent_chain_roundtrip Z degree
  right_inv := topologicalChain_current_roundtrip Z degree

/-- [proved-derived; formal-checked] The generic chain/current chart commutes with the complete
alternating boundary in every degree. -/
theorem topologicalChainEquivCurrent_boundary (Z : TopCat) (degree : ℕ)
    (chain : topologicalChain Z (degree + 1)) :
    topologicalChainEquivCurrent Z degree
        ((topologicalSingularChainComplex Z).d (degree + 1) degree chain) =
      factorBoundary (topologicalFactorSSet Z) degree
        (topologicalChainEquivCurrent Z (degree + 1) chain) := by
  let left : (topologicalSingularChainComplex Z).X (degree + 1) ⟶
      ModuleCat.of ℚ (FactorCurrent (topologicalFactorSSet Z) degree) :=
    (topologicalSingularChainComplex Z).d (degree + 1) degree ≫
      topologicalChainToCurrentMorphism Z degree
  let right : (topologicalSingularChainComplex Z).X (degree + 1) ⟶
      ModuleCat.of ℚ (FactorCurrent (topologicalFactorSSet Z) degree) :=
    topologicalChainToCurrentMorphism Z (degree + 1) ≫
      ModuleCat.ofHom (factorBoundary (topologicalFactorSSet Z) degree)
  have mapsEqual : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change topologicalChainToCurrent Z degree
        ((topologicalSingularChainComplex Z).d (degree + 1) degree
          ((Limits.Sigma.ι
            (fun _ : topologicalSimplex Z (degree + 1) => rationalCoefficient)
            simplex) coefficient)) =
      factorBoundary (topologicalFactorSSet Z) degree
        (topologicalChainToCurrent Z (degree + 1)
          ((Limits.Sigma.ι
            (fun _ : topologicalSimplex Z (degree + 1) => rationalCoefficient)
            simplex) coefficient))
    rw [sigmaInjection_eq_smul_topologicalSimplexGenerator]
    simp only [map_smul, boundary_topologicalSimplexGenerator,
      topologicalChainToCurrent_generator, factorBoundary_generator,
      factorBoundaryAtom, map_sum]
    rfl
  exact congrArg (fun morphism => morphism chain) mapsEqual

/-- The addressed simplex transported by one continuous source passage. -/
def topologicalSimplexMap {X Z : TopCat} (map : X ⟶ Z) (degree : ℕ)
    (simplex : topologicalSimplex X degree) : topologicalSimplex Z degree :=
  (TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)) simplex

/-- [proved-derived; formal-checked] Transport of addressed simplices composes exactly with
the underlying continuous passages. -/
theorem topologicalSimplexMap_comp {X Y Z : TopCat} (first : X ⟶ Y) (second : Y ⟶ Z)
    (degree : ℕ) (simplex : topologicalSimplex X degree) :
    topologicalSimplexMap (first ≫ second) degree simplex =
      topologicalSimplexMap second degree
        (topologicalSimplexMap first degree simplex) := by
  change ((TopCat.toSSet.map (first ≫ second)).app _ simplex) = _
  rw [Functor.map_comp]
  rfl

/-- [proved-derived; formal-checked] The identity passage leaves every addressed simplex
unchanged. -/
@[simp]
theorem topologicalSimplexMap_id {X : TopCat} (degree : ℕ)
    (simplex : topologicalSimplex X degree) :
    topologicalSimplexMap (𝟙 X) degree simplex = simplex := by
  simp [topologicalSimplexMap]

/-- Linear transport of the complete finite addressed-simplex population. -/
def topologicalCurrentMap {X Z : TopCat} (map : X ⟶ Z) (degree : ℕ) :
    FactorCurrent (topologicalFactorSSet X) degree →ₗ[ℚ]
      FactorCurrent (topologicalFactorSSet Z) degree :=
  extend fun simplex => generator (topologicalSimplexMap map degree simplex)

@[simp]
theorem topologicalCurrentMap_generator {X Z : TopCat} (map : X ⟶ Z)
    {degree : ℕ} (simplex : topologicalSimplex X degree) :
    topologicalCurrentMap map degree (generator simplex) =
      generator (topologicalSimplexMap map degree simplex) := by
  exact extend_generator _ _

/-- Functorial singular-chain transport sends an addressed generator to the same addressed
simplex as direct receiver-current transport. -/
theorem topologicalChainMap_simplexGenerator {X Z : TopCat} (map : X ⟶ Z)
    {degree : ℕ} (simplex : topologicalSimplex X degree) :
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map map).f degree
        (topologicalSimplexGenerator X simplex) =
      topologicalSimplexGenerator Z (topologicalSimplexMap map degree simplex) := by
  change (ModuleCat.Hom.hom (Limits.Sigma.map'
      (f := fun _ : topologicalSimplex X degree => rationalCoefficient)
      (g := fun _ : topologicalSimplex Z degree => rationalCoefficient)
      ((TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)))
      (fun _ => 𝟙 rationalCoefficient)))
      ((ModuleCat.Hom.hom
        (Limits.Sigma.ι
          (fun _ : topologicalSimplex X degree => rationalCoefficient)
          simplex)) (1 : ℚ)) = _
  have inclusion := Limits.Sigma.ι_comp_map'
    (f := fun _ : topologicalSimplex X degree => rationalCoefficient)
    (g := fun _ : topologicalSimplex Z degree => rationalCoefficient)
    ((TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)))
    (fun _ : topologicalSimplex X degree => 𝟙 rationalCoefficient) simplex
  exact congrArg (fun morphism => (ModuleCat.Hom.hom morphism) (1 : ℚ)) inclusion

/-- [proved-derived; formal-checked] Chain transport and addressed-current transport are one
natural passage, not two independently chosen maps. -/
theorem topologicalChainEquivCurrent_map {X Z : TopCat} (map : X ⟶ Z)
    (degree : ℕ) (chain : topologicalChain X degree) :
    topologicalChainEquivCurrent Z degree
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
          rationalCoefficient).map map).f degree chain) =
      topologicalCurrentMap map degree
        (topologicalChainEquivCurrent X degree chain) := by
  let left : (topologicalSingularChainComplex X).X degree ⟶
      ModuleCat.of ℚ (FactorCurrent (topologicalFactorSSet Z) degree) :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      rationalCoefficient).map map).f degree ≫
        topologicalChainToCurrentMorphism Z degree
  let right : (topologicalSingularChainComplex X).X degree ⟶
      ModuleCat.of ℚ (FactorCurrent (topologicalFactorSSet Z) degree) :=
    topologicalChainToCurrentMorphism X degree ≫
      ModuleCat.ofHom (topologicalCurrentMap map degree)
  have mapsEqual : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change topologicalChainToCurrent Z degree
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
          rationalCoefficient).map map).f degree
          ((Limits.Sigma.ι
            (fun _ : topologicalSimplex X degree => rationalCoefficient)
            simplex) coefficient)) =
      topologicalCurrentMap map degree
        (topologicalChainToCurrent X degree
          ((Limits.Sigma.ι
            (fun _ : topologicalSimplex X degree => rationalCoefficient)
            simplex) coefficient))
    rw [sigmaInjection_eq_smul_topologicalSimplexGenerator]
    simp only [map_smul, topologicalChainMap_simplexGenerator,
      topologicalChainToCurrent_generator, topologicalCurrentMap_generator]
  exact congrArg (fun morphism => morphism chain) mapsEqual

/-! ## An actual normalized sphere coefficient and the product nonboundary receiver -/

/-- The inverse chart returns every retained boundary to the actual singular complex. -/
theorem topologicalCurrentToChain_boundary (Z : TopCat) (degree : ℕ)
    (current : FactorCurrent (topologicalFactorSSet Z) (degree + 1)) :
    topologicalCurrentToChain Z degree (factorBoundary (topologicalFactorSSet Z) degree current) =
      (topologicalSingularChainComplex Z).d (degree + 1) degree
        (topologicalCurrentToChain Z (degree + 1) current) := by
  have returned := topologicalChainEquivCurrent_boundary Z degree
    (topologicalCurrentToChain Z (degree + 1) current)
  change topologicalChainToCurrent Z degree
      ((topologicalSingularChainComplex Z).d (degree + 1) degree
        (topologicalCurrentToChain Z (degree + 1) current)) =
    factorBoundary (topologicalFactorSSet Z) degree
      (topologicalChainToCurrent Z (degree + 1)
        (topologicalCurrentToChain Z (degree + 1) current)) at returned
  rw [topologicalChain_current_roundtrip] at returned
  have inverseReturn := congrArg (topologicalCurrentToChain Z degree) returned
  rw [topologicalCurrent_chain_roundtrip] at inverseReturn
  exact inverseReturn.symm

/-- No quotient of addressed degeneracies is needed to obtain boundary squared zero. -/
theorem topologicalFactorBoundary_sq (Z : TopCat.{0}) (degree : ℕ)
    (current : FactorCurrent (topologicalFactorSSet Z) (degree + 2)) :
    factorBoundary (topologicalFactorSSet Z) degree
      (factorBoundary (topologicalFactorSSet Z) (degree + 1) current) = 0 := by
  apply (topologicalChainEquivCurrent Z degree).symm.injective
  change topologicalCurrentToChain Z degree
      (factorBoundary (topologicalFactorSSet Z) degree
        (factorBoundary (topologicalFactorSSet Z) (degree + 1) current)) =
    topologicalCurrentToChain Z degree 0
  rw [topologicalCurrentToChain_boundary, topologicalCurrentToChain_boundary, map_zero]
  change (((topologicalSingularChainComplex Z).d (degree + 2) (degree + 1) ≫
    (topologicalSingularChainComplex Z).d (degree + 1) degree)
    (topologicalCurrentToChain Z (degree + 2) current)) = 0
  rw [HomologicalComplex.d_comp_d]
  rfl

section Audit

#print axioms topologicalSimplicialModule_face_generator
#print axioms boundary_topologicalSimplexGenerator
#print axioms topologicalChainToCurrent_generator
#print axioms topologicalCurrentToChain_generator
#print axioms sigmaInjection_eq_smul_topologicalSimplexGenerator
#print axioms topologicalCurrent_chain_roundtrip
#print axioms topologicalChain_current_roundtrip
#print axioms topologicalChainEquivCurrent_boundary
#print axioms topologicalSimplexMap_comp
#print axioms topologicalSimplexMap_id
#print axioms topologicalCurrentMap_generator
#print axioms topologicalChainMap_simplexGenerator
#print axioms topologicalChainEquivCurrent_map
#print axioms topologicalCurrentToChain_boundary
#print axioms topologicalFactorBoundary_sq

end Audit

end Holonics.Hodge.HodgeProductDiagonal
