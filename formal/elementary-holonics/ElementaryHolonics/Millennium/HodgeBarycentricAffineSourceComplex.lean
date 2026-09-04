import ElementaryHolonics.Millennium.HodgeBarycentricDegreeTwoFilling

/-!
# The finite affine source complex behind barycentric filling

The sphere-valued singular chain retains a parent simplex composed with an affine source map.  To
cone that current without losing lineage, this file first keeps the source maps themselves as a
free rational chain.  Its boundary is literal restriction to the three addressed source edges.
The six barycentric cells, identity cell, and nine edge-prism cells then form a closed source
current before any receiver simplex is applied.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricAffineSourceComplex

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision
open Soma.Holonics.Millennium.HodgeStellarSubdivisionHomotopy
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricSubdivisionHomotopy
open Soma.Holonics.Millennium.HodgeBarycentricDegreeTwoFilling

open CategoryTheory

/-- Free rational population of addressed triangle source maps. -/
abbrev SourceTriangleChain := C(Triangle, Triangle) →₀ ℚ

/-- Free rational population of addressed edge source maps. -/
abbrev SourceEdgeChain := C(Segment, Triangle) →₀ ℚ

def sourceTriangleGenerator (base : C(Triangle, Triangle)) : SourceTriangleChain :=
  Finsupp.single base 1

def sourceEdgeGenerator (edge : C(Segment, Triangle)) : SourceEdgeChain :=
  Finsupp.single edge 1

/-- Complete alternating source-edge boundary of one addressed triangle map. -/
def sourceTriangleBoundary (base : C(Triangle, Triangle)) : SourceEdgeChain :=
  ∑ face : Fin 3, (-1 : ℚ) ^ (face : ℕ) •
    sourceEdgeGenerator (base.comp (simplexFaceMap (degree := 1) face))

/-- Linear extension of source restriction. -/
def sourceBoundary : SourceTriangleChain →ₗ[ℚ] SourceEdgeChain :=
  Finsupp.linearCombination ℚ sourceTriangleBoundary

@[simp]
theorem sourceBoundary_single (base : C(Triangle, Triangle)) (coefficient : ℚ) :
    sourceBoundary (Finsupp.single base coefficient) =
      coefficient • sourceTriangleBoundary base := by
  simp [sourceBoundary]

/-- One edge path lifted into an addressed exterior face of the source triangle. -/
def liftedEdgeMap (outerFace : Fin 3) (edge : C(Segment, Segment)) :
    C(Segment, Triangle) :=
  (simplexFaceMap (degree := 1) outerFace).comp edge

theorem residualPrismBase_main_face_zero (outerFace : Fin 3) :
    (residualPrismBase outerFace 0).comp (simplexFaceMap (degree := 1) 0) =
      liftedEdgeMap outerFace (edgeConeMap 0) := by
  simp only [residualPrismBase, liftedEdgeMap, ContinuousMap.comp_assoc]
  rw [edgeHomotopyMainMap_face_zero]

theorem residualPrismBase_main_face_one (outerFace : Fin 3) :
    (residualPrismBase outerFace 0).comp (simplexFaceMap (degree := 1) 1) =
      simplexFaceMap (degree := 1) outerFace := by
  simp only [residualPrismBase, ContinuousMap.comp_assoc]
  rw [edgeHomotopyMainMap_face_one]
  simp

theorem residualPrismBase_main_face_two (outerFace : Fin 3) :
    (residualPrismBase outerFace 0).comp (simplexFaceMap (degree := 1) 2) =
      liftedEdgeMap outerFace reversedFirstHalfMap := by
  simp only [residualPrismBase, liftedEdgeMap, ContinuousMap.comp_assoc]
  rw [edgeHomotopyMainMap_face_two]

theorem residualPrismBase_fold_face_zero (outerFace : Fin 3) :
    (residualPrismBase outerFace 1).comp (simplexFaceMap (degree := 1) 0) =
      liftedEdgeMap outerFace reversedFirstHalfMap := by
  simp only [residualPrismBase, liftedEdgeMap, ContinuousMap.comp_assoc]
  rw [edgeHomotopyFoldMap_face_zero]

theorem residualPrismBase_fold_face_one (outerFace : Fin 3) :
    (residualPrismBase outerFace 1).comp (simplexFaceMap (degree := 1) 1) =
      liftedEdgeMap outerFace constantMidpointEdgeMap := by
  simp only [residualPrismBase, liftedEdgeMap, ContinuousMap.comp_assoc]
  rw [edgeHomotopyFoldMap_face_one]

theorem residualPrismBase_fold_face_two (outerFace : Fin 3) :
    (residualPrismBase outerFace 1).comp (simplexFaceMap (degree := 1) 2) =
      liftedEdgeMap outerFace (edgeConeMap 1) := by
  simp only [residualPrismBase, liftedEdgeMap, ContinuousMap.comp_assoc]
  rw [edgeHomotopyFoldMap_face_two]

theorem residualPrismBase_constant_face (outerFace : Fin 3) (face : Fin 3) :
    (residualPrismBase outerFace 2).comp (simplexFaceMap (degree := 1) face) =
      liftedEdgeMap outerFace constantMidpointEdgeMap := by
  simp only [residualPrismBase, liftedEdgeMap, ContinuousMap.comp_assoc]
  rw [edgeHomotopyConstantMap_face]

/-- The complete sixteen-occurrence residual before composition with a sphere simplex. -/
def sourceBarycentricResidual : SourceTriangleChain :=
  (∑ outerFace : Fin 3, ∑ half : Fin 2,
      (-1 : ℚ) ^ ((outerFace : ℕ) + (half : ℕ)) •
        sourceTriangleGenerator (barycentricTriangleMap outerFace half)) -
    sourceTriangleGenerator (ContinuousMap.id Triangle) -
    ∑ outerFace : Fin 3, (-1 : ℚ) ^ (outerFace : ℕ) •
      (sourceTriangleGenerator (residualPrismBase outerFace 0) -
        sourceTriangleGenerator (residualPrismBase outerFace 1) -
        sourceTriangleGenerator (residualPrismBase outerFace 2))

/-- The affine source residual is closed before any possibly non-injective receiver simplex is
applied.  Thus later cone cancellation cannot be an artefact of collapsed sphere images. -/
theorem sourceBoundary_sourceBarycentricResidual :
    sourceBoundary sourceBarycentricResidual = 0 := by
  classical
  rw [sourceBarycentricResidual, map_sub, map_sub, map_sum]
  simp only [sourceTriangleGenerator, map_sum, map_smul, map_sub,
    sourceBoundary_single, one_smul, sourceTriangleBoundary]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  repeat rw [Fin.sum_univ_three]
  rw [barycentricTriangleMap_face_zero 0 0,
    barycentricTriangleMap_face_zero 0 1,
    barycentricTriangleMap_face_zero 1 0,
    barycentricTriangleMap_face_zero 1 1,
    barycentricTriangleMap_face_zero 2 0,
    barycentricTriangleMap_face_zero 2 1,
    barycentricTriangleMap_midpoint_pair 0,
    barycentricTriangleMap_midpoint_pair 1,
    barycentricTriangleMap_midpoint_pair 2,
    barycentricTriangleMap_radial_two,
    barycentricTriangleMap_radial_one,
    barycentricTriangleMap_radial_zero]
  rw [residualPrismBase_main_face_zero 0,
    residualPrismBase_main_face_one 0,
    residualPrismBase_main_face_two 0,
    residualPrismBase_fold_face_zero 0,
    residualPrismBase_fold_face_one 0,
    residualPrismBase_fold_face_two 0,
    residualPrismBase_constant_face 0 0,
    residualPrismBase_constant_face 0 1,
    residualPrismBase_constant_face 0 2,
    residualPrismBase_main_face_zero 1,
    residualPrismBase_main_face_one 1,
    residualPrismBase_main_face_two 1,
    residualPrismBase_fold_face_zero 1,
    residualPrismBase_fold_face_one 1,
    residualPrismBase_fold_face_two 1,
    residualPrismBase_constant_face 1 0,
    residualPrismBase_constant_face 1 1,
    residualPrismBase_constant_face 1 2,
    residualPrismBase_main_face_zero 2,
    residualPrismBase_main_face_one 2,
    residualPrismBase_main_face_two 2,
    residualPrismBase_fold_face_zero 2,
    residualPrismBase_fold_face_one 2,
    residualPrismBase_fold_face_two 2,
    residualPrismBase_constant_face 2 0,
    residualPrismBase_constant_face 2 1,
    residualPrismBase_constant_face 2 2]
  simp only [sourceEdgeGenerator, liftedEdgeMap]
  norm_num
  module

/-! ## Common-apex realization of the closed source current -/

/-- Reparameterize one parent sphere simplex by an addressed triangle source map. -/
def reparameterizedTriangle (base : C(Triangle, Triangle))
    (simplex : SphereSingularSimplex 2) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2)) simplex).comp base)

/-- The fixed-apex affine cone on one addressed source edge. -/
def commonApexEdgeVertices (edge : C(Segment, Triangle)) : Fin 3 → Triangle :=
  Fin.cases triangleBarycenter fun vertex : Fin 2 => edge (stdSimplex.vertex vertex)

def commonApexEdgeMap (edge : C(Segment, Triangle)) : C(Triangle, Triangle) :=
  triangleAffineMap (commonApexEdgeVertices edge)

def commonApexEdgeSubsimplex (edge : C(Segment, Triangle))
    (simplex : SphereSingularSimplex 2) : SphereSingularSimplex 2 :=
  reparameterizedTriangle (commonApexEdgeMap edge) simplex

/-- Source-map realization into the degree-two singular current of the parent simplex. -/
def sourceTriangleRealization (simplex : SphereSingularSimplex 2) :
    SourceTriangleChain →ₗ[ℚ] SphereSingularChainComplex.X 2 :=
  Finsupp.linearCombination ℚ fun base =>
    simplexGenerator (reparameterizedTriangle base simplex)

/-- Source-edge cone realization with the parent simplex's barycentre as common apex. -/
def sourceEdgeConeRealization (simplex : SphereSingularSimplex 2) :
    SourceEdgeChain →ₗ[ℚ] SphereSingularChainComplex.X 2 :=
  Finsupp.linearCombination ℚ fun edge =>
    simplexGenerator (commonApexEdgeSubsimplex edge simplex)

/-- Source-triangle cone realization into degree three. -/
def sourceTriangleConeRealization (simplex : SphereSingularSimplex 2) :
    SourceTriangleChain →ₗ[ℚ] SphereSingularChainComplex.X 3 :=
  Finsupp.linearCombination ℚ fun base =>
    simplexGenerator (conedTriangleSubsimplex base simplex)

@[simp]
theorem sourceTriangleRealization_single (simplex : SphereSingularSimplex 2)
    (base : C(Triangle, Triangle)) (coefficient : ℚ) :
    sourceTriangleRealization simplex (Finsupp.single base coefficient) =
      coefficient • simplexGenerator (reparameterizedTriangle base simplex) := by
  simp [sourceTriangleRealization]

@[simp]
theorem sourceEdgeConeRealization_single (simplex : SphereSingularSimplex 2)
    (edge : C(Segment, Triangle)) (coefficient : ℚ) :
    sourceEdgeConeRealization simplex (Finsupp.single edge coefficient) =
      coefficient • simplexGenerator (commonApexEdgeSubsimplex edge simplex) := by
  simp [sourceEdgeConeRealization]

@[simp]
theorem sourceTriangleConeRealization_single (simplex : SphereSingularSimplex 2)
    (base : C(Triangle, Triangle)) (coefficient : ℚ) :
    sourceTriangleConeRealization simplex (Finsupp.single base coefficient) =
      coefficient • simplexGenerator (conedTriangleSubsimplex base simplex) := by
  simp [sourceTriangleConeRealization]

theorem coneOverTriangleFaceMap_eq_commonApexEdgeMap
    (base : C(Triangle, Triangle)) (omitted : Fin 3) :
    coneOverTriangleFaceMap base omitted =
      commonApexEdgeMap (base.comp (simplexFaceMap (degree := 1) omitted)) := by
  rfl

theorem conedTriangleSubsimplex_face_succ_commonApex
    (base : C(Triangle, Triangle)) (omitted : Fin 3)
    (simplex : SphereSingularSimplex 2) :
    simplexFace omitted.succ (conedTriangleSubsimplex base simplex) =
      commonApexEdgeSubsimplex
        (base.comp (simplexFaceMap (degree := 1) omitted)) simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [conedTriangleSubsimplex, commonApexEdgeSubsimplex,
    reparameterizedTriangle, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, coneOverTriangleMap_face_succ,
    coneOverTriangleFaceMap_eq_commonApexEdgeMap]

theorem conedTriangleSubsimplex_face_zero_affine
    (vertices : Fin 3 → Triangle) (simplex : SphereSingularSimplex 2) :
    simplexFace 0
        (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
      reparameterizedTriangle (triangleAffineMap vertices) simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [conedTriangleSubsimplex, reparameterizedTriangle,
    Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, coneOverTriangleMap_face_zero_affine]

/-- Boundary of one affine common-apex cone: its exterior base minus the common-apex realization
of its complete source boundary. -/
theorem boundary_sourceTriangleConeRealization_single_affine
    (vertices : Fin 3 → Triangle) (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (triangleAffineMap vertices))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (triangleAffineMap vertices)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (triangleAffineMap vertices))) := by
  classical
  have hfaceOne :
      simplexFace 1
          (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
        commonApexEdgeSubsimplex
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 0)) simplex := by
    simpa using conedTriangleSubsimplex_face_succ_commonApex
      (triangleAffineMap vertices) 0 simplex
  have hfaceTwo :
      simplexFace 2
          (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
        commonApexEdgeSubsimplex
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 1)) simplex := by
    simpa using conedTriangleSubsimplex_face_succ_commonApex
      (triangleAffineMap vertices) 1 simplex
  have hfaceThree :
      simplexFace 3
          (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
        commonApexEdgeSubsimplex
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 2)) simplex := by
    simpa using conedTriangleSubsimplex_face_succ_commonApex
      (triangleAffineMap vertices) 2 simplex
  simp only [sourceTriangleGenerator, sourceTriangleConeRealization_single,
    sourceTriangleRealization_single, sourceBoundary_single,
    sourceTriangleBoundary, one_smul,
    boundary_simplexGenerator]
  rw [Fin.sum_univ_four]
  repeat rw [Fin.sum_univ_three]
  rw [conedTriangleSubsimplex_face_zero_affine, hfaceOne, hfaceTwo, hfaceThree]
  simp only [map_add, map_smul, sourceEdgeGenerator,
    sourceEdgeConeRealization_single, one_smul]
  norm_num
  module

/-- The identity source triangle is affine with its three canonical vertices. -/
theorem triangleAffineMap_canonicalVertices :
    triangleAffineMap (fun vertex : Fin 3 => stdSimplex.vertex vertex) =
      ContinuousMap.id Triangle := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  fin_cases coordinate <;>
    simp [triangleAffineMap_apply, Fin.sum_univ_three]

/-- Every lifted edge-prism base is affine.  The returned vertex chart is exact, so the common
apex cone retains the entire base rather than merely its three samples. -/
theorem residualPrismBase_eq_triangleAffineMap_vertices
    (outerFace : Fin 3) (kind : Fin 3) :
    residualPrismBase outerFace kind =
      triangleAffineMap (fun vertex =>
        residualPrismBase outerFace kind (stdSimplex.vertex vertex)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  fin_cases outerFace <;> fin_cases kind <;> fin_cases coordinate <;>
    simp [residualPrismBase, edgeHomotopyMainMap, edgeHomotopyFoldMap,
      edgeHomotopyConstantMap, triangleToSegmentAffineMap_apply,
      triangleAffineMap_apply, Fin.sum_univ_three]

theorem boundary_sourceTriangleConeRealization_barycentric
    (outerFace : Fin 3) (half : Fin 2) (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (barycentricTriangleMap outerFace half))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (barycentricTriangleMap outerFace half)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (barycentricTriangleMap outerFace half))) := by
  exact boundary_sourceTriangleConeRealization_single_affine
    (barycentricTriangleVertices outerFace half) simplex

theorem boundary_sourceTriangleConeRealization_id
    (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (ContinuousMap.id Triangle))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (ContinuousMap.id Triangle)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (ContinuousMap.id Triangle))) := by
  simpa only [triangleAffineMap_canonicalVertices] using
    boundary_sourceTriangleConeRealization_single_affine
      (fun vertex : Fin 3 => stdSimplex.vertex vertex) simplex

theorem boundary_sourceTriangleConeRealization_prism
    (outerFace : Fin 3) (kind : Fin 3) (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (residualPrismBase outerFace kind))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (residualPrismBase outerFace kind)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (residualPrismBase outerFace kind))) := by
  rw [residualPrismBase_eq_triangleAffineMap_vertices]
  exact boundary_sourceTriangleConeRealization_single_affine _ simplex

/-- The common-apex cone fills the universal source residual up to the cone of its source
boundary.  This is the exact chain-contraction identity before closedness is consumed. -/
theorem boundary_sourceTriangleConeRealization_sourceBarycentricResidual
    (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex sourceBarycentricResidual) =
      sourceTriangleRealization simplex sourceBarycentricResidual -
        sourceEdgeConeRealization simplex
          (sourceBoundary sourceBarycentricResidual) := by
  classical
  rw [sourceBarycentricResidual]
  simp only [map_sub, map_sum, map_smul]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  rw [boundary_sourceTriangleConeRealization_barycentric 0 0,
    boundary_sourceTriangleConeRealization_barycentric 0 1,
    boundary_sourceTriangleConeRealization_barycentric 1 0,
    boundary_sourceTriangleConeRealization_barycentric 1 1,
    boundary_sourceTriangleConeRealization_barycentric 2 0,
    boundary_sourceTriangleConeRealization_barycentric 2 1,
    boundary_sourceTriangleConeRealization_id,
    boundary_sourceTriangleConeRealization_prism 0 0,
    boundary_sourceTriangleConeRealization_prism 0 1,
    boundary_sourceTriangleConeRealization_prism 0 2,
    boundary_sourceTriangleConeRealization_prism 1 0,
    boundary_sourceTriangleConeRealization_prism 1 1,
    boundary_sourceTriangleConeRealization_prism 1 2,
    boundary_sourceTriangleConeRealization_prism 2 0,
    boundary_sourceTriangleConeRealization_prism 2 1,
    boundary_sourceTriangleConeRealization_prism 2 2]
  module

/-- Closedness removes the entire side-face population, so the common-apex cone returns the
sixteen-term source residual exactly. -/
theorem boundary_sourceTriangleConeRealization_sourceBarycentricResidual_eq_realization
    (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex sourceBarycentricResidual) =
      sourceTriangleRealization simplex sourceBarycentricResidual := by
  rw [boundary_sourceTriangleConeRealization_sourceBarycentricResidual,
    sourceBoundary_sourceBarycentricResidual, map_zero, sub_zero]

theorem reparameterizedTriangle_barycentric (outerFace : Fin 3) (half : Fin 2)
    (simplex : SphereSingularSimplex 2) :
    reparameterizedTriangle (barycentricTriangleMap outerFace half) simplex =
      barycentricTriangleSubsimplex outerFace half simplex := rfl

theorem reparameterizedTriangle_id (simplex : SphereSingularSimplex 2) :
    reparameterizedTriangle (ContinuousMap.id Triangle) simplex = simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  simp [reparameterizedTriangle]

/-- The three prism kinds, after lifting into one outer face of the parent triangle, reconstruct
the exact degree-one homotopy triangles already used by `P₁∂`. -/
theorem reparameterizedTriangle_residualPrismBase
    (outerFace : Fin 3) (kind : Fin 3) (simplex : SphereSingularSimplex 2) :
    reparameterizedTriangle (residualPrismBase outerFace kind) simplex =
      edgeHomotopyTriangle
        (match kind with
        | 0 => edgeHomotopyMainMap
        | 1 => edgeHomotopyFoldMap
        | _ => edgeHomotopyConstantMap)
        (simplexFace outerFace simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  simp only [reparameterizedTriangle, residualPrismBase, edgeHomotopyTriangle,
    Equiv.apply_symm_apply]
  rw [simplexFace_realization, ContinuousMap.comp_assoc]
  rfl

/-- The universal affine source current realizes to the exact recursive degree-two defect on each
addressed sphere simplex. -/
theorem sourceTriangleRealization_sourceBarycentricResidual
    (simplex : SphereSingularSimplex 2) :
    sourceTriangleRealization simplex sourceBarycentricResidual =
      barycentricTriangleHomotopyDefectMorphism (simplexGenerator simplex) := by
  classical
  rw [sourceBarycentricResidual]
  simp only [map_sub, map_sum, map_smul, sourceTriangleGenerator,
    sourceTriangleRealization_single, one_smul]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  rw [reparameterizedTriangle_barycentric 0 0,
    reparameterizedTriangle_barycentric 0 1,
    reparameterizedTriangle_barycentric 1 0,
    reparameterizedTriangle_barycentric 1 1,
    reparameterizedTriangle_barycentric 2 0,
    reparameterizedTriangle_barycentric 2 1,
    reparameterizedTriangle_id,
    reparameterizedTriangle_residualPrismBase 0 0,
    reparameterizedTriangle_residualPrismBase 0 1,
    reparameterizedTriangle_residualPrismBase 0 2,
    reparameterizedTriangle_residualPrismBase 1 0,
    reparameterizedTriangle_residualPrismBase 1 1,
    reparameterizedTriangle_residualPrismBase 1 2,
    reparameterizedTriangle_residualPrismBase 2 0,
    reparameterizedTriangle_residualPrismBase 2 1,
    reparameterizedTriangle_residualPrismBase 2 2]
  rw [barycentricTriangleHomotopyDefectMorphism]
  change _ =
    barycentricTriangleSubdivisionMorphism (simplexGenerator simplex) -
      simplexGenerator simplex -
      barycentricEdgeSubdivisionHomotopyMorphism
        (SphereSingularChainComplex.d 2 1 (simplexGenerator simplex))
  rw [barycentricTriangleSubdivisionMorphism_simplexGenerator,
    boundary_simplexGenerator, map_sum]
  simp only [map_smul,
    barycentricEdgeSubdivisionHomotopyMorphism_simplexGenerator,
    barycentricTriangleSubdivision, barycentricEdgeSubdivisionHomotopy]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]

/-- The explicit common-apex three-current attached to one addressed parent triangle. -/
abbrev barycentricDegreeTwoHomotopy (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.X 3 :=
  sourceTriangleConeRealization simplex sourceBarycentricResidual

/-- Its boundary is the complete recursive defect, with all side faces discharged by source-level
closedness. -/
theorem boundary_barycentricDegreeTwoHomotopy (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2 (barycentricDegreeTwoHomotopy simplex) =
      barycentricTriangleHomotopyDefectMorphism (simplexGenerator simplex) := by
  rw [barycentricDegreeTwoHomotopy,
    boundary_sourceTriangleConeRealization_sourceBarycentricResidual_eq_realization,
    sourceTriangleRealization_sourceBarycentricResidual]

/-- Coproduct-linear extension of the explicit degree-two source cone. -/
private def barycentricDegreeTwoHomotopyComponent (simplex : SphereSingularSimplex 2) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 3 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • barycentricDegreeTwoHomotopy simplex
      map_add' := fun left right => add_smul left right _
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply]
        exact smul_assoc scalar coefficient (barycentricDegreeTwoHomotopy simplex) }

abbrev barycentricDegreeTwoHomotopyMorphism :
    SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 3 :=
  Limits.Sigma.desc fun simplex =>
    barycentricDegreeTwoHomotopyComponent simplex

@[simp]
theorem barycentricDegreeTwoHomotopyMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 2) :
    barycentricDegreeTwoHomotopyMorphism (simplexGenerator simplex) =
      barycentricDegreeTwoHomotopy simplex := by
  have hι := Limits.Sigma.ι_desc
    (fun source => barycentricDegreeTwoHomotopyComponent source) simplex
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => barycentricDegreeTwoHomotopyComponent source))
      (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- The formerly conditional `P₂∂ = R₂` square is now inhabited by the source-faithful affine
cone. -/
theorem barycentricDegreeTwoHomotopyMorphism_comp_boundary :
    barycentricDegreeTwoHomotopyMorphism ≫
        SphereSingularChainComplex.d 3 2 =
      barycentricTriangleHomotopyDefectMorphism := by
  apply Limits.Sigma.hom_ext
  intro simplex
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change (barycentricDegreeTwoHomotopyMorphism ≫ SphereSingularChainComplex.d 3 2)
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex) coefficient) =
    barycentricTriangleHomotopyDefectMorphism
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex) coefficient)
  rw [Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
  rw [ModuleCat.comp_apply, map_smul, barycentricDegreeTwoHomotopyMorphism_simplexGenerator,
    map_smul, boundary_barycentricDegreeTwoHomotopy, map_smul]

/-- The exact degree-two filling required by the recursive barycentric chain homotopy. -/
def barycentricDegreeTwoFilling :
    HodgeBarycentricSubdivisionHomotopy.BarycentricDegreeTwoFilling where
  fill := barycentricDegreeTwoHomotopyMorphism
  boundary := barycentricDegreeTwoHomotopyMorphism_comp_boundary

/-- The resulting degree-three current is now unconditional and satisfies the exact recursive
chain square with the six-cell barycentric degree-two current. -/
def recursiveBarycentricDegreeThreeMorphism :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 3 :=
  barycentricDegreeTwoFilling.correctedDegreeThreeMorphism

theorem recursiveBarycentricDegreeThreeMorphism_comp_boundary :
    recursiveBarycentricDegreeThreeMorphism ≫
        SphereSingularChainComplex.d 3 2 =
      SphereSingularChainComplex.d 3 2 ≫
        barycentricTriangleSubdivisionMorphism :=
  barycentricDegreeTwoFilling.correctedDegreeThreeMorphism_comp_boundary

section Audit

#print axioms sourceBoundary_sourceBarycentricResidual
#print axioms boundary_sourceTriangleConeRealization_single_affine
#print axioms residualPrismBase_eq_triangleAffineMap_vertices
#print axioms boundary_sourceTriangleConeRealization_sourceBarycentricResidual_eq_realization
#print axioms boundary_barycentricDegreeTwoHomotopy
#print axioms barycentricDegreeTwoHomotopyMorphism_comp_boundary
#print axioms recursiveBarycentricDegreeThreeMorphism_comp_boundary

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricAffineSourceComplex
