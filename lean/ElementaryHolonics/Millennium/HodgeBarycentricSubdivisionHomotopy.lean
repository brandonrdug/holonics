import ElementaryHolonics.Millennium.HodgeBarycentricCoverSmallness

/-!
# The first recursive homotopy for barycentric subdivision

Edge refinement is geometrically contracting, but the Hodge carrier also needs an exact proof that
it preserves the represented class.  This file constructs that proof in degree one.  The main
triangle sweeps the original edge through its midpoint split.  A folded triangle and one constant
triangle retain the orientation-reversal fibre which singular chains do not quotient away.  Their
signed boundary is exactly barycentric edge subdivision minus the original edge.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricSubdivisionHomotopy

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision

/-- Affine transport from a triangle into the addressed source segment. -/
def triangleToSegmentAffineMap (vertices : Fin 3 → Segment) : C(Triangle, Segment) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 3,
      point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex)
          (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 2, ∑ vertex : Fin 3,
            point vertex * vertices vertex coordinate =
          ∑ vertex : Fin 3, ∑ coordinate : Fin 2,
            point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 3, point vertex * 1 := by
          apply Finset.sum_congr rfl
          intro vertex _
          rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
        _ = 1 := by simp [stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun coordinate =>
      continuous_finset_sum _ fun vertex _ =>
        ((continuous_apply vertex).comp continuous_subtype_val).mul continuous_const

@[simp]
theorem triangleToSegmentAffineMap_apply (vertices : Fin 3 → Segment)
    (point : Triangle) (coordinate : Fin 2) :
    triangleToSegmentAffineMap vertices point coordinate =
      ∑ vertex : Fin 3, point vertex * vertices vertex coordinate := rfl

/-- Restricting an affine triangle-to-segment map to a face retains exactly the two addressed
vertices of that face. -/
theorem triangleToSegmentAffineMap_face (vertices : Fin 3 → Segment)
    (omitted : Fin 3) :
    (triangleToSegmentAffineMap vertices).comp
        (simplexFaceMap (degree := 1) omitted) =
      segmentAffineMap (fun edgeVertex => vertices (omitted.succAbove edgeVertex)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) omitted point vertex * vertices vertex coordinate) =
    ∑ edgeVertex : Fin 2,
      point edgeVertex * vertices (omitted.succAbove edgeVertex) coordinate
  fin_cases omitted <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_three, Fin.sum_univ_two, Fin.succAbove]

/-- The main sweep has ordered vertices `[initial endpoint, midpoint, terminal endpoint]`. -/
def edgeHomotopyMainVertices : Fin 3 → Segment :=
  ![stdSimplex.vertex 0, segmentMidpoint, stdSimplex.vertex 1]

/-- The fold retains the parametrically reversed first half rather than identifying it with a
negative generator. -/
def edgeHomotopyFoldVertices : Fin 3 → Segment :=
  ![segmentMidpoint, stdSimplex.vertex 0, segmentMidpoint]

/-- The constant cell cancels the degenerate edge left by the fold. -/
def edgeHomotopyConstantVertices : Fin 3 → Segment :=
  fun _ => segmentMidpoint

/-- The reversed first half is retained as a distinct singular occurrence. -/
def reversedFirstHalfMap : C(Segment, Segment) :=
  segmentAffineMap ![stdSimplex.vertex 0, segmentMidpoint]

/-- The constant midpoint edge is retained until its two-dimensional cancellation is proved. -/
def constantMidpointEdgeMap : C(Segment, Segment) :=
  segmentAffineMap (fun _ => segmentMidpoint)

def edgeHomotopyMainMap : C(Triangle, Segment) :=
  triangleToSegmentAffineMap edgeHomotopyMainVertices

def edgeHomotopyFoldMap : C(Triangle, Segment) :=
  triangleToSegmentAffineMap edgeHomotopyFoldVertices

def edgeHomotopyConstantMap : C(Triangle, Segment) :=
  triangleToSegmentAffineMap edgeHomotopyConstantVertices

theorem edgeHomotopyMainMap_face_zero :
    edgeHomotopyMainMap.comp (simplexFaceMap (degree := 1) 0) = edgeConeMap 0 := by
  rw [edgeHomotopyMainMap, triangleToSegmentAffineMap_face]
  apply congrArg segmentAffineMap
  funext vertex
  fin_cases vertex <;> rfl

theorem segmentAffineMap_endpoints :
    segmentAffineMap ![stdSimplex.vertex 0, stdSimplex.vertex 1] =
      ContinuousMap.id Segment := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  fin_cases coordinate <;> simp [segmentAffineMap_apply, Fin.sum_univ_two]

theorem edgeHomotopyMainMap_face_one :
    edgeHomotopyMainMap.comp (simplexFaceMap (degree := 1) 1) =
      ContinuousMap.id Segment := by
  rw [edgeHomotopyMainMap, triangleToSegmentAffineMap_face]
  exact segmentAffineMap_endpoints

theorem edgeHomotopyMainMap_face_two :
    edgeHomotopyMainMap.comp (simplexFaceMap (degree := 1) 2) =
      reversedFirstHalfMap := by
  rw [edgeHomotopyMainMap, triangleToSegmentAffineMap_face, reversedFirstHalfMap]
  apply congrArg segmentAffineMap
  funext vertex
  fin_cases vertex <;> rfl

theorem edgeHomotopyFoldMap_face_zero :
    edgeHomotopyFoldMap.comp (simplexFaceMap (degree := 1) 0) =
      reversedFirstHalfMap := by
  rw [edgeHomotopyFoldMap, triangleToSegmentAffineMap_face, reversedFirstHalfMap]
  apply congrArg segmentAffineMap
  funext vertex
  fin_cases vertex <;> rfl

theorem edgeHomotopyFoldMap_face_one :
    edgeHomotopyFoldMap.comp (simplexFaceMap (degree := 1) 1) =
      constantMidpointEdgeMap := by
  rw [edgeHomotopyFoldMap, triangleToSegmentAffineMap_face, constantMidpointEdgeMap]
  apply congrArg segmentAffineMap
  funext vertex
  fin_cases vertex <;> rfl

theorem edgeHomotopyFoldMap_face_two :
    edgeHomotopyFoldMap.comp (simplexFaceMap (degree := 1) 2) = edgeConeMap 1 := by
  rw [edgeHomotopyFoldMap, triangleToSegmentAffineMap_face]
  apply congrArg segmentAffineMap
  funext vertex
  fin_cases vertex <;> rfl

theorem edgeHomotopyConstantMap_face (omitted : Fin 3) :
    edgeHomotopyConstantMap.comp (simplexFaceMap (degree := 1) omitted) =
      constantMidpointEdgeMap := by
  rw [edgeHomotopyConstantMap, triangleToSegmentAffineMap_face,
    constantMidpointEdgeMap]
  apply congrArg segmentAffineMap
  funext vertex
  rfl

/-- Reparametrize an addressed singular edge without quotienting its source map. -/
def reparameterizedEdge (sourceMap : C(Segment, Segment))
    (simplex : SphereSingularSimplex 1) : SphereSingularSimplex 1 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 1)) simplex).comp sourceMap)

/-- Fill an addressed singular edge by one explicit triangular source sweep. -/
def edgeHomotopyTriangle (sourceMap : C(Triangle, Segment))
    (simplex : SphereSingularSimplex 1) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 1)) simplex).comp sourceMap)

theorem edgeHomotopyTriangle_face_eq
    (sourceMap : C(Triangle, Segment)) (face : Fin 3)
    (edgeMap : C(Segment, Segment))
    (hmap : sourceMap.comp (simplexFaceMap (degree := 1) face) = edgeMap)
    (simplex : SphereSingularSimplex 1) :
    simplexFace face (edgeHomotopyTriangle sourceMap simplex) =
      reparameterizedEdge edgeMap simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization]
  simp only [edgeHomotopyTriangle, reparameterizedEdge, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, hmap]

theorem reparameterizedEdge_edgeConeMap (omitted : Fin 2)
    (simplex : SphereSingularSimplex 1) :
    reparameterizedEdge (edgeConeMap omitted) simplex =
      barycentricEdgeSubsimplex omitted simplex := rfl

theorem reparameterizedEdge_id (simplex : SphereSingularSimplex 1) :
    reparameterizedEdge (ContinuousMap.id Segment) simplex = simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  simp [reparameterizedEdge]

def reversedFirstHalfSubsimplex (simplex : SphereSingularSimplex 1) :
    SphereSingularSimplex 1 := reparameterizedEdge reversedFirstHalfMap simplex

def constantMidpointEdgeSubsimplex (simplex : SphereSingularSimplex 1) :
    SphereSingularSimplex 1 := reparameterizedEdge constantMidpointEdgeMap simplex

theorem edgeHomotopyMain_face_zero (simplex : SphereSingularSimplex 1) :
    simplexFace 0 (edgeHomotopyTriangle edgeHomotopyMainMap simplex) =
      barycentricEdgeSubsimplex 0 simplex := by
  rw [← reparameterizedEdge_edgeConeMap]
  exact edgeHomotopyTriangle_face_eq _ _ _ edgeHomotopyMainMap_face_zero simplex

theorem edgeHomotopyMain_face_one (simplex : SphereSingularSimplex 1) :
    simplexFace 1 (edgeHomotopyTriangle edgeHomotopyMainMap simplex) = simplex := by
  rw [← reparameterizedEdge_id simplex]
  exact edgeHomotopyTriangle_face_eq _ _ _ edgeHomotopyMainMap_face_one simplex

theorem edgeHomotopyMain_face_two (simplex : SphereSingularSimplex 1) :
    simplexFace 2 (edgeHomotopyTriangle edgeHomotopyMainMap simplex) =
      reversedFirstHalfSubsimplex simplex := by
  exact edgeHomotopyTriangle_face_eq _ _ _ edgeHomotopyMainMap_face_two simplex

theorem edgeHomotopyFold_face_zero (simplex : SphereSingularSimplex 1) :
    simplexFace 0 (edgeHomotopyTriangle edgeHomotopyFoldMap simplex) =
      reversedFirstHalfSubsimplex simplex := by
  exact edgeHomotopyTriangle_face_eq _ _ _ edgeHomotopyFoldMap_face_zero simplex

theorem edgeHomotopyFold_face_one (simplex : SphereSingularSimplex 1) :
    simplexFace 1 (edgeHomotopyTriangle edgeHomotopyFoldMap simplex) =
      constantMidpointEdgeSubsimplex simplex := by
  exact edgeHomotopyTriangle_face_eq _ _ _ edgeHomotopyFoldMap_face_one simplex

theorem edgeHomotopyFold_face_two (simplex : SphereSingularSimplex 1) :
    simplexFace 2 (edgeHomotopyTriangle edgeHomotopyFoldMap simplex) =
      barycentricEdgeSubsimplex 1 simplex := by
  rw [← reparameterizedEdge_edgeConeMap]
  exact edgeHomotopyTriangle_face_eq _ _ _ edgeHomotopyFoldMap_face_two simplex

theorem edgeHomotopyConstant_face (face : Fin 3)
    (simplex : SphereSingularSimplex 1) :
    simplexFace face (edgeHomotopyTriangle edgeHomotopyConstantMap simplex) =
      constantMidpointEdgeSubsimplex simplex := by
  exact edgeHomotopyTriangle_face_eq _ _ _
    (edgeHomotopyConstantMap_face face) simplex

/-- Three retained source triangles form the exact prism between the original edge and its
midpoint subdivision. -/
def barycentricEdgeSubdivisionHomotopy (simplex : SphereSingularSimplex 1) :
    SphereChain 2 :=
  simplexGenerator (edgeHomotopyTriangle edgeHomotopyMainMap simplex) -
    simplexGenerator (edgeHomotopyTriangle edgeHomotopyFoldMap simplex) -
      simplexGenerator (edgeHomotopyTriangle edgeHomotopyConstantMap simplex)

/-- The exact degree-one homotopy law.  Reversed parametrization and the constant edge cancel by
explicit filled occurrences; neither is silently identified with a sign or deleted. -/
theorem boundary_barycentricEdgeSubdivisionHomotopy
    (simplex : SphereSingularSimplex 1) :
    SphereSingularChainComplex.d 2 1
        (barycentricEdgeSubdivisionHomotopy simplex) =
      barycentricEdgeSubdivision simplex - simplexGenerator simplex := by
  rw [barycentricEdgeSubdivisionHomotopy, map_sub, map_sub]
  simp only [boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_three]
  rw [edgeHomotopyMain_face_zero, edgeHomotopyMain_face_one,
    edgeHomotopyMain_face_two, edgeHomotopyFold_face_zero,
    edgeHomotopyFold_face_one, edgeHomotopyFold_face_two,
    edgeHomotopyConstant_face 0, edgeHomotopyConstant_face 1,
    edgeHomotopyConstant_face 2]
  rw [barycentricEdgeSubdivision, Fin.sum_univ_two]
  norm_num
  module

/-- Coproduct-linear extension of the explicit edge prism. -/
def barycentricEdgeSubdivisionHomotopyMorphism :
    SphereSingularChainComplex.X 1 ⟶ SphereSingularChainComplex.X 2 :=
  Limits.Sigma.desc fun simplex =>
    ModuleCat.ofHom
      { toFun := fun coefficient =>
          coefficient • barycentricEdgeSubdivisionHomotopy simplex
        map_add' := fun left right => add_smul left right _
        map_smul' := by
          intro scalar coefficient
          simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
          rfl }

@[simp]
theorem barycentricEdgeSubdivisionHomotopyMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 1) :
    barycentricEdgeSubdivisionHomotopyMorphism (simplexGenerator simplex) =
      barycentricEdgeSubdivisionHomotopy simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 1 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => ModuleCat.ofHom
          { toFun := fun coefficient : ℚ =>
              coefficient • barycentricEdgeSubdivisionHomotopy source
            map_add' := fun left right => add_smul left right _
            map_smul' := by
              intro scalar coefficient
              simp only [RingHom.id_apply, smul_eq_mul, mul_smul] })) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- The local prism linearizes to the exact degree-one chain-homotopy equation. -/
theorem barycentricEdgeSubdivisionHomotopyMorphism_comp_boundary :
    barycentricEdgeSubdivisionHomotopyMorphism ≫
        SphereSingularChainComplex.d 2 1 =
      barycentricEdgeSubdivisionMorphism - 𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro simplex
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change ℚ at coefficient
  simp only [ConcreteCategory.comp_apply]
  rw [Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
  change SphereSingularChainComplex.d 2 1
      (barycentricEdgeSubdivisionHomotopyMorphism
        (coefficient • simplexGenerator simplex)) =
    barycentricEdgeSubdivisionMorphism (coefficient • simplexGenerator simplex) -
      coefficient • simplexGenerator simplex
  simp only [map_smul,
    barycentricEdgeSubdivisionHomotopyMorphism_simplexGenerator,
    boundary_barycentricEdgeSubdivisionHomotopy,
    barycentricEdgeSubdivisionMorphism_simplexGenerator]
  exact smul_sub (M := ℚ) (A := SphereChain 1) coefficient
    (barycentricEdgeSubdivision simplex) (simplexGenerator simplex)

/-- The exact degree-two source current which the next cone must fill.  It is subdivision minus
identity after removing the already-accounted edge-prism current. -/
def barycentricTriangleHomotopyDefectMorphism :
    SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 2 :=
  barycentricTriangleSubdivisionMorphism - 𝟙 _ -
    SphereSingularChainComplex.d 2 1 ≫
      barycentricEdgeSubdivisionHomotopyMorphism

/-- The recursive defect is a genuine cycle.  This is the algebraic condition which makes coning
lawful; it follows from the two checked chain squares and the exact degree-one prism, rather than
from an assumed contractibility slogan. -/
theorem barycentricTriangleHomotopyDefectMorphism_comp_boundary :
    barycentricTriangleHomotopyDefectMorphism ≫
        SphereSingularChainComplex.d 2 1 = 0 := by
  rw [barycentricTriangleHomotopyDefectMorphism,
    Preadditive.sub_comp, Preadditive.sub_comp,
    barycentricTriangleSubdivisionMorphism_comp_boundary,
    Category.id_comp, Category.assoc,
    barycentricEdgeSubdivisionHomotopyMorphism_comp_boundary,
    Preadditive.comp_sub, Category.comp_id]
  module

theorem boundary_barycentricTriangleHomotopyDefect (chain : SphereChain 2) :
    SphereSingularChainComplex.d 2 1
        (barycentricTriangleHomotopyDefectMorphism chain) = 0 := by
  simpa using
    congrArg (fun morphism : SphereSingularChainComplex.X 2 ⟶
      SphereSingularChainComplex.X 1 => morphism chain)
      barycentricTriangleHomotopyDefectMorphism_comp_boundary

/-- The remaining geometric datum is now exact: a filling of the constructed recursive defect.
No boundary or compatibility hypothesis remains hidden in the type. -/
structure BarycentricDegreeTwoFilling where
  fill : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 3
  boundary : fill ≫ SphereSingularChainComplex.d 3 2 =
    barycentricTriangleHomotopyDefectMorphism

namespace BarycentricDegreeTwoFilling

/-- Correct the exterior-preserving tetrahedral current by the supplied defect filling. -/
def correctedDegreeThreeMorphism (filling : BarycentricDegreeTwoFilling) :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 3 :=
  tetrahedralStellarSubdivisionMorphism +
    SphereSingularChainComplex.d 3 2 ≫ filling.fill

/-- Every actual filling of the one exposed cycle automatically returns the required recursive
degree-`3 → 2` chain square. -/
theorem correctedDegreeThreeMorphism_comp_boundary
    (filling : BarycentricDegreeTwoFilling) :
    filling.correctedDegreeThreeMorphism ≫
        SphereSingularChainComplex.d 3 2 =
      SphereSingularChainComplex.d 3 2 ≫
        barycentricTriangleSubdivisionMorphism := by
  rw [correctedDegreeThreeMorphism, Preadditive.add_comp,
    tetrahedralStellarSubdivisionMorphism_comp_boundary,
    Category.assoc, filling.boundary,
    barycentricTriangleHomotopyDefectMorphism,
    Preadditive.comp_sub, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc,
    SphereSingularChainComplex.d_comp_d, CategoryTheory.Limits.zero_comp]
  module

end BarycentricDegreeTwoFilling

section Audit

#print axioms triangleToSegmentAffineMap_face
#print axioms boundary_barycentricEdgeSubdivisionHomotopy
#print axioms barycentricEdgeSubdivisionHomotopyMorphism_comp_boundary
#print axioms barycentricTriangleHomotopyDefectMorphism_comp_boundary
#print axioms BarycentricDegreeTwoFilling.correctedDegreeThreeMorphism_comp_boundary

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricSubdivisionHomotopy
