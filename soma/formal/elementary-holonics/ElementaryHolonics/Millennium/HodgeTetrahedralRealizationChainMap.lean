import ElementaryHolonics.Millennium.HodgeTetrahedralChainComplex

/-!
# The complete tetrahedral-to-singular realization chain map

The four radial face simplices and their six shared edge simplices were already realized in the
singular complex of `S²`.  This file retains the four vertex occurrences as well, proves every
realized edge has terminal-minus-initial singular boundary, and assembles the face, edge, and
vertex maps into one genuine chain map from the finite tetrahedral complex.

The map is the geometric inclusion direction.  The remaining Hodge detector construction is a
source-authentic chain retraction in the other direction; this file does not choose such a
retraction or assign arbitrary seam-crossing singular simplices to tetrahedral cells.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralRealizationChainMap

open CategoryTheory
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex

/-- Equality of two tetrahedral vertex occurrences is proved by equality of the complete ordered
three-stage face inclusion, not by equality of a sampled point. -/
theorem radialSingularSimplex_vertex_eq_of_composite_eq
    (firstFace secondFace : Fin 4)
    (firstEdge secondEdge : Fin 3)
    (firstVertex secondVertex : Fin 2)
    (hcomposite :
      firstFace.succAbove ∘ firstEdge.succAbove ∘ firstVertex.succAbove =
        secondFace.succAbove ∘ secondEdge.succAbove ∘ secondVertex.succAbove) :
    simplexFace firstVertex (simplexFace firstEdge (radialSingularSimplex firstFace)) =
      simplexFace secondVertex (simplexFace secondEdge (radialSingularSimplex secondFace)) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 0))).injective
  rw [simplexFace_realization, simplexFace_realization]
  rw [simplexFace_realization, simplexFace_realization]
  simp only [radialSingularSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  apply Subtype.ext
  change NormedSpace.normalize
      (centeredFaceVector firstFace
        (stdSimplex.map (SimplexCategory.δ firstEdge).toOrderHom
          (stdSimplex.map (SimplexCategory.δ firstVertex).toOrderHom point))) =
    NormedSpace.normalize
      (centeredFaceVector secondFace
        (stdSimplex.map (SimplexCategory.δ secondEdge).toOrderHom
          (stdSimplex.map (SimplexCategory.δ secondVertex).toOrderHom point)))
  congr 1
  unfold centeredFaceVector tetraFace
  simp only [SimplexCategory.δ]
  simp only [stdSimplex.map_comp_apply]
  have hcomposite' :
      firstFace.succAbove ∘
          ⇑(SimplexCategory.Hom.toOrderHom
            (SimplexCategory.mkHom firstEdge.succAboveOrderEmb.toOrderHom)) ∘
          ⇑(SimplexCategory.Hom.toOrderHom
            (SimplexCategory.mkHom firstVertex.succAboveOrderEmb.toOrderHom)) =
        secondFace.succAbove ∘
          ⇑(SimplexCategory.Hom.toOrderHom
            (SimplexCategory.mkHom secondEdge.succAboveOrderEmb.toOrderHom)) ∘
          ⇑(SimplexCategory.Hom.toOrderHom
            (SimplexCategory.mkHom secondVertex.succAboveOrderEmb.toOrderHom)) := by
    funext i
    have hi := congrFun hcomposite i
    simpa [Function.comp_apply, Fin.succAboveOrderEmb_apply] using hi
  rw [hcomposite']

/-- Four addressed singular vertices, selected from the already realized tetrahedral edges. -/
def vertexSimplex : TetraVertex → SphereSingularSimplex 0
  | 0 => simplexFace 1 (edgeSimplex .e01)
  | 1 => simplexFace 0 (edgeSimplex .e01)
  | 2 => simplexFace 0 (edgeSimplex .e02)
  | 3 => simplexFace 0 (edgeSimplex .e03)

theorem edgeSimplex_terminal (edge : TetraEdge) :
    simplexFace 0 (edgeSimplex edge) = vertexSimplex (edgeTerminal edge) := by
  cases edge with
  | e01 => rfl
  | e02 => rfl
  | e03 => rfl
  | e12 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl
  | e13 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl
  | e23 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl

theorem edgeSimplex_initial (edge : TetraEdge) :
    simplexFace 1 (edgeSimplex edge) = vertexSimplex (edgeInitial edge) := by
  cases edge with
  | e01 => rfl
  | e02 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl
  | e03 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl
  | e12 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl
  | e13 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl
  | e23 =>
      apply radialSingularSimplex_vertex_eq_of_composite_eq
      funext vertex
      fin_cases vertex <;> rfl

theorem boundary_edgeSimplex (edge : TetraEdge) :
    SphereSingularChainComplex.d 1 0 (simplexGenerator (edgeSimplex edge)) =
      simplexGenerator (vertexSimplex (edgeTerminal edge)) -
        simplexGenerator (vertexSimplex (edgeInitial edge)) := by
  rw [boundary_simplexGenerator, Fin.sum_univ_two]
  norm_num
  rw [edgeSimplex_terminal, edgeSimplex_initial]
  simp only [sub_eq_add_neg]

/-- Linear realization of the four finite vertex occurrences. -/
def vertexRealization : VertexChain →ₗ[ℚ] SphereChain 0 where
  toFun chain :=
    chain 0 • simplexGenerator (vertexSimplex 0) +
    chain 1 • simplexGenerator (vertexSimplex 1) +
    chain 2 • simplexGenerator (vertexSimplex 2) +
    chain 3 • simplexGenerator (vertexSimplex 3)
  map_add' left right := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' scalar chain := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_add, smul_smul, smul_eq_mul]

/-- The lower realization square commutes for every addressed finite edge chain. -/
theorem edgeRealization_boundary (chain : EdgeChain) :
    SphereSingularChainComplex.d 1 0 (edgeRealization chain) =
      vertexRealization (vertexBoundary chain) := by
  change SphereSingularChainComplex.d 1 0
      (chain .e01 • simplexGenerator (edgeSimplex .e01) +
       chain .e02 • simplexGenerator (edgeSimplex .e02) +
       chain .e03 • simplexGenerator (edgeSimplex .e03) +
       chain .e12 • simplexGenerator (edgeSimplex .e12) +
       chain .e13 • simplexGenerator (edgeSimplex .e13) +
       chain .e23 • simplexGenerator (edgeSimplex .e23)) =
    (-chain .e01 - chain .e02 - chain .e03) • simplexGenerator (vertexSimplex 0) +
      (chain .e01 - chain .e12 - chain .e13) • simplexGenerator (vertexSimplex 1) +
      (chain .e02 + chain .e12 - chain .e23) • simplexGenerator (vertexSimplex 2) +
      (chain .e03 + chain .e13 + chain .e23) • simplexGenerator (vertexSimplex 3)
  simp only [map_add, map_smul, boundary_edgeSimplex]
  simp only [edgeTerminal, edgeInitial]
  module

/-- The degreewise realization of the complete finite tetrahedral carrier. -/
def tetrahedralRealizationComponent : (degree : ℕ) →
    tetrahedralChainComplex.X degree ⟶ SphereSingularChainComplex.X degree
  | 0 => ModuleCat.ofHom vertexRealization
  | 1 => ModuleCat.ofHom edgeRealization
  | 2 => ModuleCat.ofHom faceRealization
  | _ + 3 => 0

theorem tetrahedralRealizationComponent_comm (degree : ℕ) :
    tetrahedralRealizationComponent (degree + 1) ≫
        SphereSingularChainComplex.d (degree + 1) degree =
      tetrahedralChainComplex.d (degree + 1) degree ≫
        tetrahedralRealizationComponent degree := by
  cases degree with
  | zero =>
      ext chain
      exact edgeRealization_boundary chain
  | succ degree =>
      cases degree with
      | zero =>
          ext chain
          exact faceRealization_boundary chain
      | succ degree =>
          cases degree with
          | zero =>
              have hcomponent : tetrahedralRealizationComponent 3 = 0 := rfl
              rw [hcomponent, Limits.zero_comp, tetrahedralChainComplex_d_three_two,
                Limits.zero_comp]
          | succ degree =>
              have hcomponent :
                  tetrahedralRealizationComponent (degree + 4) = 0 := rfl
              have hdifferential :
                  tetrahedralChainComplex.d (degree + 4) (degree + 3) = 0 := by
                exact ChainComplex.of_d tetrahedralChainModule tetrahedralDifferential (degree + 3)
              rw [hcomponent, Limits.zero_comp, hdifferential, Limits.zero_comp]

/-- The four faces, six edges, and four vertices form one geometric chain map into rational
singular chains on `S²`. -/
def tetrahedralRealizationChainMap :
    tetrahedralChainComplex ⟶ SphereSingularChainComplex where
  f := tetrahedralRealizationComponent
  comm' := by
    intro sourceDegree targetDegree related
    change targetDegree + 1 = sourceDegree at related
    subst sourceDegree
    exact tetrahedralRealizationComponent_comm targetDegree

@[simp]
theorem tetrahedralRealizationChainMap_f_two :
    tetrahedralRealizationChainMap.f 2 =
      ModuleCat.ofHom faceRealization := rfl

section Audit

#print axioms radialSingularSimplex_vertex_eq_of_composite_eq
#print axioms edgeSimplex_terminal
#print axioms edgeSimplex_initial
#print axioms boundary_edgeSimplex
#print axioms edgeRealization_boundary
#print axioms tetrahedralRealizationComponent_comm
#print axioms tetrahedralRealizationChainMap

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralRealizationChainMap
