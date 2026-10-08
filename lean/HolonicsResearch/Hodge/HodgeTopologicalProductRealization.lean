import HolonicsResearch.Foundation.ProductDegreeTwo
import HolonicsResearch.Hodge.HodgeSphereProductRulingProjections
import HolonicsResearch.Hodge.HodgeSphereHomologyEquivalence
import HolonicsResearch.Hodge.HodgeSphereFundamentalDetector
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Topological product simplex realization

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

section Audit

#print axioms split_join_topologicalProductSimplex
#print axioms join_split_topologicalProductSimplex
#print axioms splitTopologicalProductSimplex_face
#print axioms homeomorphicTopologicalProductSimplexEquiv_face

end Audit

end Holonics.Hodge.HodgeProductDiagonal
