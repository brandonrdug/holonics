import ElementaryHolonics.Foundation.ProductDegreeTwo
import ElementaryHolonics.Millennium.HodgeSphereProductRulingProjections

/-!
# The genuine sphere-product chain as a diagonal holonic current

The generic diagonal transport becomes relevant to the Hodge receiver only after its occurrence
population is identified with the genuine singular simplices of `S² × S²`.  This file constructs
that identification exactly.  A product-valued continuous simplex is equivalent to the ordered
pair of its coordinate simplices, and the categorical coproduct of rational generator lines is
equivalent to the free finite current on those occurrences.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProductDiagonal

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Soma.Holonics.DiagonalChainTransport
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeSphereProductRulingProjections

universe u

/-! ## The topological-product realization, once for every pair of spaces -/

/-- The actual product topology of two admitted topological carriers. -/
abbrev topologicalProductTopCat (X Y : TopCat.{u}) : TopCat.{u} := TopCat.of (X × Y)

abbrev topologicalFactorSSet (X : TopCat.{u}) : SSet.{u} := TopCat.toSSet.obj X

abbrev topologicalProductSSet (X Y : TopCat.{u}) : SSet.{u} :=
  TopCat.toSSet.obj (topologicalProductTopCat X Y)

/-- The first coordinate current as a continuous map before categorical bundling. -/
def topologicalFirstProjectionContinuousMap (X Y : TopCat.{u}) : C(X × Y, X) where
  toFun point := point.1
  continuous_toFun := continuous_fst

/-- The second coordinate current as a continuous map before categorical bundling. -/
def topologicalSecondProjectionContinuousMap (X Y : TopCat.{u}) : C(X × Y, Y) where
  toFun point := point.2
  continuous_toFun := continuous_snd

def topologicalFirstProjection (X Y : TopCat.{u}) :
    topologicalProductTopCat X Y ⟶ X :=
  TopCat.ofHom (topologicalFirstProjectionContinuousMap X Y)

def topologicalSecondProjection (X Y : TopCat.{u}) :
    topologicalProductTopCat X Y ⟶ Y :=
  TopCat.ofHom (topologicalSecondProjectionContinuousMap X Y)

/-- Split one genuine continuous product simplex into both coordinate simplices. -/
def splitTopologicalProductSimplex (X Y : TopCat.{u}) {degree : ℕ}
    (simplex : Simplex (topologicalProductSSet X Y) degree) :
    DiagonalOccurrence (topologicalFactorSSet X) (topologicalFactorSSet Y) degree :=
  ((TopCat.toSSet.map (topologicalFirstProjection X Y)).app
      (Opposite.op (SimplexCategory.mk degree)) simplex,
    (TopCat.toSSet.map (topologicalSecondProjection X Y)).app
      (Opposite.op (SimplexCategory.mk degree)) simplex)

/-- Rejoin two coordinate simplices into their complete continuous product simplex. -/
def joinTopologicalProductSimplex (X Y : TopCat.{u}) {degree : ℕ}
    (pair : DiagonalOccurrence
      (topologicalFactorSSet X) (topologicalFactorSSet Y) degree) :
    Simplex (topologicalProductSSet X Y) degree :=
  (TopCat.toSSetObjEquiv (topologicalProductTopCat X Y)
    (Opposite.op (SimplexCategory.mk degree))).symm
      ((TopCat.toSSetObjEquiv X
          (Opposite.op (SimplexCategory.mk degree)) pair.1).prodMk
        (TopCat.toSSetObjEquiv Y
          (Opposite.op (SimplexCategory.mk degree)) pair.2))

theorem split_join_topologicalProductSimplex (X Y : TopCat.{u}) {degree : ℕ}
    (pair : DiagonalOccurrence
      (topologicalFactorSSet X) (topologicalFactorSSet Y) degree) :
    splitTopologicalProductSimplex X Y
        (joinTopologicalProductSimplex X Y pair) = pair := by
  rcases pair with ⟨left, right⟩
  apply Prod.ext
  · apply (TopCat.toSSetObjEquiv X
      (Opposite.op (SimplexCategory.mk degree))).injective
    apply ContinuousMap.ext
    intro point
    rfl
  · apply (TopCat.toSSetObjEquiv Y
      (Opposite.op (SimplexCategory.mk degree))).injective
    apply ContinuousMap.ext
    intro point
    rfl

theorem join_split_topologicalProductSimplex (X Y : TopCat.{u}) {degree : ℕ}
    (simplex : Simplex (topologicalProductSSet X Y) degree) :
    joinTopologicalProductSimplex X Y
        (splitTopologicalProductSimplex X Y simplex) = simplex := by
  apply (TopCat.toSSetObjEquiv (topologicalProductTopCat X Y)
    (Opposite.op (SimplexCategory.mk degree))).injective
  apply ContinuousMap.ext
  intro point
  apply Prod.ext <;> rfl

/-- [proved-derived; formal-checked] Genuine product simplices and diagonal coordinate pairs are
the same occurrence population in every degree. -/
def topologicalProductSimplexEquiv (X Y : TopCat.{u}) (degree : ℕ) :
    Simplex (topologicalProductSSet X Y) degree ≃
      DiagonalOccurrence (topologicalFactorSSet X) (topologicalFactorSSet Y) degree where
  toFun := splitTopologicalProductSimplex X Y
  invFun := joinTopologicalProductSimplex X Y
  left_inv := join_split_topologicalProductSimplex X Y
  right_inv := split_join_topologicalProductSimplex X Y

theorem splitTopologicalProductSimplex_face (X Y : TopCat.{u}) {degree : ℕ}
    (omitted : Fin (degree + 2))
    (simplex : Simplex (topologicalProductSSet X Y) (degree + 1)) :
    splitTopologicalProductSimplex X Y (face omitted simplex) =
      diagonalFace omitted (splitTopologicalProductSimplex X Y simplex) := by
  apply Prod.ext
  · exact SSet.δ_naturality_apply
      (TopCat.toSSet.map (topologicalFirstProjection X Y)) omitted simplex
  · exact SSet.δ_naturality_apply
      (TopCat.toSSet.map (topologicalSecondProjection X Y)) omitted simplex

/-- [proved-derived; formal-checked] Every actual topological product supplies the exact
face-natural realization consumed by the generic product contraction. -/
def topologicalProductSimplexRealization (X Y : TopCat.{u}) :
    ProductSimplexRealization (topologicalProductSSet X Y)
      (topologicalFactorSSet X) (topologicalFactorSSet Y) where
  simplexEquiv := topologicalProductSimplexEquiv X Y
  face_naturality := splitTopologicalProductSimplex_face X Y

/-- A carrier known homeomorphic to a product inherits the same complete coordinate-simplex
realization.  This is the chart-change owner needed by recursive products: the homeomorphism is
retained as an isomorphism before the diagonal product chart is applied. -/
def homeomorphicTopologicalProductSimplexEquiv
    (Z X Y : TopCat.{u}) (productIso : Z ≅ topologicalProductTopCat X Y)
    (degree : ℕ) :
    Simplex (topologicalFactorSSet Z) degree ≃
      DiagonalOccurrence (topologicalFactorSSet X) (topologicalFactorSSet Y) degree :=
  ((TopCat.toSSet.mapIso productIso).app
      (Opposite.op (SimplexCategory.mk degree))).toEquiv.trans
    (topologicalProductSimplexEquiv X Y degree)

theorem homeomorphicTopologicalProductSimplexEquiv_face
    (Z X Y : TopCat.{u}) (productIso : Z ≅ topologicalProductTopCat X Y)
    {degree : ℕ} (omitted : Fin (degree + 2))
    (simplex : Simplex (topologicalFactorSSet Z) (degree + 1)) :
    homeomorphicTopologicalProductSimplexEquiv Z X Y productIso degree
        (face omitted simplex) =
      diagonalFace omitted
        (homeomorphicTopologicalProductSimplexEquiv Z X Y productIso (degree + 1) simplex) := by
  change splitTopologicalProductSimplex X Y
      ((TopCat.toSSet.map productIso.hom).app
        (Opposite.op (SimplexCategory.mk degree)) (face omitted simplex)) =
    diagonalFace omitted
      (splitTopologicalProductSimplex X Y
        ((TopCat.toSSet.map productIso.hom).app
          (Opposite.op (SimplexCategory.mk (degree + 1))) simplex))
  have transportedFace :
      (TopCat.toSSet.map productIso.hom).app
          (Opposite.op (SimplexCategory.mk degree)) (face omitted simplex) =
        face omitted
          ((TopCat.toSSet.map productIso.hom).app
            (Opposite.op (SimplexCategory.mk (degree + 1))) simplex) := by
    exact SSet.δ_naturality_apply
      (TopCat.toSSet.map productIso.hom) omitted simplex
  rw [transportedFace]
  exact splitTopologicalProductSimplex_face X Y omitted _

/-- [proved-derived; formal-checked] A homeomorphism to a product transports all low-degree
product contraction data without identifying the carrier with the product definitionally. -/
def homeomorphicTopologicalProductSimplexRealization
    (Z X Y : TopCat.{u}) (productIso : Z ≅ topologicalProductTopCat X Y) :
    ProductSimplexRealization (topologicalFactorSSet Z)
      (topologicalFactorSSet X) (topologicalFactorSSet Y) where
  simplexEquiv := homeomorphicTopologicalProductSimplexEquiv Z X Y productIso
  face_naturality :=
    homeomorphicTopologicalProductSimplexEquiv_face Z X Y productIso

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

/-- [proved-derived; formal-checked] The actual singular boundary of one product triangle becomes
the componentwise diagonal boundary with no lost simplex occurrence. -/
theorem productChainDiagonalEquiv_boundary_generator (simplex : ProductSimplex 2) :
    productChainDiagonalEquiv 1
        (SphereProductSingularChainComplex.d 2 1 (productSimplexGenerator simplex)) =
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 (productSimplexGenerator simplex)) := by
  rw [boundary_productSimplexGenerator, map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_generator]
  change _ = extend diagonalBoundaryTwoAtom (generator (splitProductSimplex simplex))
  rw [extend_generator]
  change (∑ omitted : Fin 3, (-1 : ℚ) ^ (omitted : ℕ) •
      generator (splitProductSimplex (productSimplexFace omitted simplex))) =
    diagonalBoundaryTwoAtom (splitProductSimplex simplex)
  simp_rw [splitProductSimplex_face]
  rw [Fin.sum_univ_three]
  norm_num [diagonalBoundaryTwoAtom]
  module

/-- [proved-derived; formal-checked] The genuine singular boundary of one product tetrahedron
becomes the four-face diagonal boundary with every source occurrence retained. -/
theorem productChainDiagonalEquiv_boundary_three_generator
    (simplex : ProductSimplex 3) :
    productChainDiagonalEquiv 2
        (SphereProductSingularChainComplex.d 3 2 (productSimplexGenerator simplex)) =
      diagonalBoundaryThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3 (productSimplexGenerator simplex)) := by
  rw [boundary_productSimplexGenerator, map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_generator]
  change _ = extend diagonalBoundaryThreeAtom (generator (splitProductSimplex simplex))
  rw [extend_generator]
  change (∑ omitted : Fin 4, (-1 : ℚ) ^ (omitted : ℕ) •
      generator (splitProductSimplex (productSimplexFace omitted simplex))) =
    diagonalBoundaryThreeAtom (splitProductSimplex simplex)
  simp_rw [splitProductSimplex_face]
  rw [Fin.sum_univ_four]
  norm_num [diagonalBoundaryThreeAtom]
  module

/-- [proved-derived; formal-checked] The genuine singular boundary square commutes on every
rational product two-chain.  Thus the generic diagonal separation holon is now attached to the
actual `S² × S²` source rather than to an isolated word fixture. -/
theorem productChainDiagonalEquiv_boundary (chain : ProductChain 2) :
    productChainDiagonalEquiv 1 (SphereProductSingularChainComplex.d 2 1 chain) =
      diagonalBoundaryTwo SphereSSet SphereSSet (productChainDiagonalEquiv 2 chain) := by
  let left : SphereProductSingularChainComplex.X 2 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 1)) :=
    SphereProductSingularChainComplex.d 2 1 ≫
      productChainDiagonalMorphism 1
  let right : SphereProductSingularChainComplex.X 2 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 1)) :=
    separatedBoundaryAfterDiagonalMorphism
  have mapsEqual : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    simp only [left, right]
    change productChainDiagonalEquiv 1
        (SphereProductSingularChainComplex.d 2 1
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 2 => rationalCoefficient) simplex) coefficient)) =
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 2 => rationalCoefficient) simplex) coefficient))
    rw [sigmaInjection_eq_smul_productGenerator]
    simp only [map_smul]
    exact congrArg (coefficient • ·)
      (productChainDiagonalEquiv_boundary_generator simplex)
  exact congrArg (fun morphism => morphism chain) mapsEqual

/-- [proved-derived; formal-checked] The genuine degree-three singular boundary square commutes on
every rational product chain. -/
theorem productChainDiagonalEquiv_boundary_three (chain : ProductChain 3) :
    productChainDiagonalEquiv 2 (SphereProductSingularChainComplex.d 3 2 chain) =
      diagonalBoundaryThree SphereSSet SphereSSet (productChainDiagonalEquiv 3 chain) := by
  let left : SphereProductSingularChainComplex.X 3 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 2)) :=
    SphereProductSingularChainComplex.d 3 2 ≫ productChainDiagonalMorphism 2
  let right : SphereProductSingularChainComplex.X 3 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 2)) :=
    ModuleCat.ofHom ((diagonalBoundaryThree SphereSSet SphereSSet).comp
      (productChainDiagonalEquiv 3).toLinearMap)
  have mapsEqual : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    simp only [left, right]
    change productChainDiagonalEquiv 2
        (SphereProductSingularChainComplex.d 3 2
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 3 => rationalCoefficient) simplex) coefficient)) =
      diagonalBoundaryThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 3 => rationalCoefficient) simplex) coefficient))
    rw [sigmaInjection_eq_smul_productGenerator]
    simp only [map_smul]
    exact congrArg (coefficient • ·)
      (productChainDiagonalEquiv_boundary_three_generator simplex)
  exact congrArg (fun morphism => morphism chain) mapsEqual

/-- The four-axis Alexander--Whitney current of one genuine product three-chain. -/
def separatedProductThreeChain (chain : ProductChain 3) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  separateThree SphereSSet SphereSSet (productChainDiagonalEquiv 3 chain)

/-- [proved-derived; formal-checked] The boundary of a genuine product three-chain separates as
an actual four-axis boundary.  This closes the boundary-compatibility half of the product
degree-two homology passage; the remaining reduction concerns the homology of the separated
axes, not whether source boundaries survive the receiver. -/
theorem separatedProductThreeChain_boundary (chain : ProductChain 3) :
    totalBoundaryThree SphereSSet SphereSSet (separatedProductThreeChain chain) =
      separateTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2
          (SphereProductSingularChainComplex.d 3 2 chain)) := by
  have law := LinearMap.congr_fun
    (boundary_separateThree SphereSSet SphereSSet)
    (productChainDiagonalEquiv 3 chain)
  change totalBoundaryThree SphereSSet SphereSSet
      (separateThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3 chain)) =
    separateTwo SphereSSet SphereSSet
      (diagonalBoundaryThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3 chain)) at law
  rw [← productChainDiagonalEquiv_boundary_three] at law
  exact law

/-- [proved-derived; formal-checked] Product boundary separation as one elementary boundary
holon.  Every source tetrahedral occurrence returns all four separated axes, and the receiver
retains the exact degree-two source boundary rather than only its vanishing homology class. -/
def productBoundarySeparationHolon :
    Soma.Holonics.BoundaryHolon
      (Current (TotalTwoOccurrence SphereSSet SphereSSet))
      (Current (TotalThreeOccurrence SphereSSet SphereSSet)) where
  Occurrence := ProductChain 3
  source _ := 0
  target chain :=
    separateTwo SphereSSet SphereSSet
      (productChainDiagonalEquiv 2
        (SphereProductSingularChainComplex.d 3 2 chain))
  receive := separatedProductThreeChain
  boundary := (totalBoundaryThree SphereSSet SphereSSet).toAddMonoidHom
  returnsBoundary := by
    intro chain
    change totalBoundaryThree SphereSSet SphereSSet
        (separatedProductThreeChain chain) =
      separateTwo SphereSSet SphereSSet
          (productChainDiagonalEquiv 2
            (SphereProductSingularChainComplex.d 3 2 chain)) - 0
    simpa using separatedProductThreeChain_boundary chain

/-- Genuine closed product two-currents, retaining the categorical singular-chain occurrence. -/
abbrev ProductTwoCycle :=
  LinearMap.ker (SphereProductSingularChainComplex.d 2 1).hom

/-- The complete separated `0×2 + 1×1 + 2×0` current of a genuine product cycle. -/
def separatedProductCycle (cycle : ProductTwoCycle) :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  separateTwo SphereSSet SphereSSet (productChainDiagonalEquiv 2 cycle.1)

theorem separatedProductCycle_boundary (cycle : ProductTwoCycle) :
    totalBoundaryTwo SphereSSet SphereSSet (separatedProductCycle cycle) = 0 := by
  have diagonalClosed :
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1) = 0 := by
    rw [← productChainDiagonalEquiv_boundary, cycle.2, map_zero]
  have transportLaw := LinearMap.congr_fun
    (boundary_separateTwo SphereSSet SphereSSet)
    (productChainDiagonalEquiv 2 cycle.1)
  simp only [LinearMap.comp_apply, diagonalClosed, map_zero] at transportLaw
  exact transportLaw

/-- [proved-derived; formal-checked] Genuine closed sphere-product currents instantiate the
generic diagonal separation boundary holon.  Its receiver keeps all three axes and its
reconstruction fibre keeps the originating singular cycle. -/
def productCycleSeparationHolon :
    Soma.Holonics.BoundaryHolon
      (Current (TotalOneOccurrence SphereSSet SphereSSet))
      (Current (TotalTwoOccurrence SphereSSet SphereSSet)) where
  Occurrence := ProductTwoCycle
  source _ := 0
  target _ := 0
  receive := separatedProductCycle
  boundary := (totalBoundaryTwo SphereSSet SphereSSet).toAddMonoidHom
  returnsBoundary := by
    intro cycle
    change totalBoundaryTwo SphereSSet SphereSSet (separatedProductCycle cycle) = 0 - 0
    simpa using separatedProductCycle_boundary cycle

/-- Reconstruct a genuine singular product chain from a separated three-axis current. -/
def rejoinedProductChain
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) : ProductChain 2 :=
  (productChainDiagonalEquiv 2).symm
    (rejoinTwo SphereSSet SphereSSet current)

/-- Reconstruct a genuine singular product three-chain from all four separated axes.  The two
interior axes retain their complete three-shuffle populations. -/
def rejoinedProductThreeChain
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) : ProductChain 3 :=
  (productChainDiagonalEquiv 3).symm
    (rejoinThree SphereSSet SphereSSet current)

/-- [proved-derived; formal-checked] The boundary of the four-axis reconstruction is the genuine
product-chain reconstruction of the separated boundary.  Consequently every filler constructed
in the separated total complex returns an actual singular boundary in `S² × S²`. -/
theorem rejoinedProductThreeChain_boundary
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) :
    SphereProductSingularChainComplex.d 3 2 (rejoinedProductThreeChain current) =
      rejoinedProductChain
        (totalBoundaryThree SphereSSet SphereSSet current) := by
  apply (productChainDiagonalEquiv 2).injective
  rw [productChainDiagonalEquiv_boundary_three,
    rejoinedProductThreeChain, LinearEquiv.apply_symm_apply]
  change diagonalBoundaryThree SphereSSet SphereSSet
      (rejoinThree SphereSSet SphereSSet current) =
    productChainDiagonalEquiv 2
      ((productChainDiagonalEquiv 2).symm
        (rejoinTwo SphereSSet SphereSSet
          (totalBoundaryThree SphereSSet SphereSSet current)))
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun
    (boundary_rejoinThree SphereSSet SphereSSet) current

/-- [proved-derived; formal-checked] A separated degree-two boundary rejoins to a genuine product
singular boundary, with the complete degree-three occurrence population as reconstruction fibre. -/
theorem rejoinedProductChain_of_separatedBoundary
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) :
    rejoinedProductChain (totalBoundaryThree SphereSSet SphereSSet current) =
      SphereProductSingularChainComplex.d 3 2
        (rejoinedProductThreeChain current) :=
  (rejoinedProductThreeChain_boundary current).symm

/-- [proved-derived; formal-checked] The boundary of the reconstructed genuine chain is exactly
the rejoined boundary of the separated current, viewed in the diagonal chart. -/
theorem productChainDiagonalEquiv_boundary_rejoined
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    productChainDiagonalEquiv 1
        (SphereProductSingularChainComplex.d 2 1 (rejoinedProductChain current)) =
      rejoinOne SphereSSet SphereSSet
        (totalBoundaryTwo SphereSSet SphereSSet current) := by
  rw [productChainDiagonalEquiv_boundary]
  rw [rejoinedProductChain, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (boundary_rejoinTwo SphereSSet SphereSSet) current

/-- A closed separated product current. -/
abbrev ClosedSeparatedProductCurrent :=
  LinearMap.ker (totalBoundaryTwo SphereSSet SphereSSet)

theorem rejoinedProductChain_boundary
    (current : ClosedSeparatedProductCurrent) :
    SphereProductSingularChainComplex.d 2 1 (rejoinedProductChain current.1) = 0 := by
  apply (productChainDiagonalEquiv 1).injective
  rw [map_zero, productChainDiagonalEquiv_boundary_rejoined, current.2, map_zero]

/-- [proved-derived; formal-checked] Every closed separated current reconstructs a genuine closed
singular product cycle. -/
def rejoinedProductCycle (current : ClosedSeparatedProductCurrent) : ProductTwoCycle :=
  ⟨rejoinedProductChain current.1, rejoinedProductChain_boundary current⟩

/-- The genuine product-chain residue after exact axis separation and ordered-shuffle
reconstruction.  This retains the full singular source occurrence rather than passing to a
normalized or endpoint-only quotient. -/
def productRoundTripDefectChain (chain : ProductChain 2) : ProductChain 2 :=
  rejoinedProductChain
      (separateTwo SphereSSet SphereSSet (productChainDiagonalEquiv 2 chain)) - chain

/-- [proved-derived; formal-checked] In the diagonal chart, the genuine singular-chain residue is
exactly the generic retained reconstruction defect. -/
theorem productRoundTripDefectChain_diagonal (chain : ProductChain 2) :
    productChainDiagonalEquiv 2 (productRoundTripDefectChain chain) =
      diagonalRoundTripDefectTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 chain) := by
  simp [productRoundTripDefectChain, rejoinedProductChain,
    diagonalRoundTripDefectTwo]

/-- [proved-derived; formal-checked] Separation followed by rejoining changes every genuine
product two-cycle by a genuine closed singular two-cycle.  The precise remaining reconstruction
obligation is to fill this returned cycle uniformly in degree three. -/
theorem productRoundTripDefectChain_boundary (cycle : ProductTwoCycle) :
    SphereProductSingularChainComplex.d 2 1
      (productRoundTripDefectChain cycle.1) = 0 := by
  apply (productChainDiagonalEquiv 1).injective
  rw [map_zero, productChainDiagonalEquiv_boundary,
    productRoundTripDefectChain_diagonal]
  have diagonalClosed :
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1) = 0 := by
    rw [← productChainDiagonalEquiv_boundary, cycle.2, map_zero]
  have law := LinearMap.congr_fun
    (boundary_diagonalRoundTripDefectTwo SphereSSet SphereSSet)
      (productChainDiagonalEquiv 2 cycle.1)
  change diagonalBoundaryTwo SphereSSet SphereSSet
      (diagonalRoundTripDefectTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1)) =
    diagonalRoundTripDefectOne SphereSSet SphereSSet
      (diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1)) at law
  rw [law, diagonalClosed]
  simp [diagonalRoundTripDefectOne]

/-- The exact closed reconstruction defect returned by one genuine product cycle. -/
def productRoundTripDefectCycle (cycle : ProductTwoCycle) : ProductTwoCycle :=
  ⟨productRoundTripDefectChain cycle.1,
    productRoundTripDefectChain_boundary cycle⟩

/-- The explicit genuine degree-three singular chain filling the complete reconstruction defect. -/
def productRoundTripDefectFillerChain (cycle : ProductTwoCycle) : ProductChain 3 :=
  (productChainDiagonalEquiv 3).symm
    (diagonalReconstructionFillerTwo SphereSSet SphereSSet
      (productChainDiagonalEquiv 2 cycle.1))

/-- [proved-derived; formal-checked] The genuine sphere-product separate--shuffle round trip is
chain-homotopic to the identity in degree two, with the complete source occurrence and four-term
degree-three filler retained. -/
theorem productRoundTripDefectFillerChain_boundary (cycle : ProductTwoCycle) :
    SphereProductSingularChainComplex.d 3 2
        (productRoundTripDefectFillerChain cycle) =
      productRoundTripDefectChain cycle.1 := by
  apply (productChainDiagonalEquiv 2).injective
  rw [productChainDiagonalEquiv_boundary_three,
    productRoundTripDefectFillerChain, LinearEquiv.apply_symm_apply,
    productRoundTripDefectChain_diagonal]
  have diagonalClosed :
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1) = 0 := by
    rw [← productChainDiagonalEquiv_boundary, cycle.2, map_zero]
  exact (diagonalRoundTripDefectTwo_eq_boundary_of_cycle
    (productChainDiagonalEquiv 2 cycle.1) diagonalClosed).symm

/-- [proved-derived; formal-checked] The reconstruction is an actual boundary holon: its source is
the original genuine product cycle, its target is its separated-and-rejoined chain, and its current
is the explicit four-term degree-three filler. -/
def productReconstructionBoundaryHolon :
    Soma.Holonics.BoundaryHolon (ProductChain 2) (ProductChain 3) where
  Occurrence := ProductTwoCycle
  source cycle := cycle.1
  target cycle := rejoinedProductChain (separatedProductCycle cycle)
  receive := productRoundTripDefectFillerChain
  boundary := (SphereProductSingularChainComplex.d 3 2).hom.toAddMonoidHom
  returnsBoundary := by
    intro cycle
    change SphereProductSingularChainComplex.d 3 2
        (productRoundTripDefectFillerChain cycle) =
      rejoinedProductChain (separatedProductCycle cycle) - cycle.1
    rw [productRoundTripDefectFillerChain_boundary]
    rfl

section Audit

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

end Soma.Holonics.Millennium.HodgeProductDiagonal
