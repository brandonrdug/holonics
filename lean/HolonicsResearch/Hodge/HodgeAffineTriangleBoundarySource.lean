import HolonicsResearch.Hodge.HodgeBarycentricDegreeTwoFilling

/-!
# The finite affine source complex behind barycentric filling

The sphere-valued singular chain retains a parent simplex composed with an affine source map.  To
cone that current without losing lineage, this file first keeps the source maps themselves as a
free rational chain.  Its boundary is literal restriction to the three addressed source edges.
The six barycentric cells, identity cell, and nine edge-prism cells then form a closed source
current before any receiver simplex is applied.
-/

noncomputable section

namespace Holonics.Hodge.HodgeBarycentricAffineSourceComplex

open Holonics.Hodge.HodgeProjectiveLineSingularReduction
open Holonics.Hodge.HodgeTwoSphereFundamentalCycle
open Holonics.Hodge.HodgeStellarSubdivision
open Holonics.Hodge.HodgeStellarSubdivisionHomotopy
open Holonics.Hodge.HodgeBarycentricEdgeSubdivision
open Holonics.Hodge.HodgeBarycentricTriangleSubdivision
open Holonics.Hodge.HodgeBarycentricSubdivisionHomotopy
open Holonics.Hodge.HodgeBarycentricDegreeTwoFilling

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


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceBoundary_sourceBarycentricResidual
