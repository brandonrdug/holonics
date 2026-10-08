import HolonicsResearch.Hodge.HodgeAffineTriangleSource
import HolonicsResearch.Hodge.HodgeBarycentricTetrahedron

/-!
# The complete free affine triangle cone returns its source current.

This is one source owner of the canonical affine complex. Existing declarations
keep their namespace; the canonical entry imports the complete source family.
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

open Holonics.Hodge.HodgeTetrahedralStellarSubdivision
open Holonics.Hodge.HodgeBarycentricTetrahedron

/-! ## The next current retains its free affine source before reception

The free cone return below is not inferred by cancelling a sphere receiver.  It restricts
the actual source maps.  Its consumer is the eighty-nine-occurrence degree-three residual.
These additions are prepared source until the shared queue admits this complete owner.
-/

open Holonics.Hodge.HodgeTetrahedralStellarSubdivision
open Holonics.Hodge.HodgeBarycentricTetrahedron

/-- The actual degree-three maps into the source triangle, before any sphere receiver. -/
abbrev SourceConedTriangleChain := C(Tetrahedron, Triangle) →₀ ℚ

/-- Alternate restriction of the retained tetrahedral map, still in the source triangle. -/
def sourceConedTriangleBoundary : SourceConedTriangleChain →ₗ[ℚ] SourceTriangleChain :=
  Finsupp.linearCombination ℚ fun base =>
    ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
      sourceTriangleGenerator (base.comp (simplexFaceMap (degree := 2) face))

/-- The same common-apex cone as the accepted sphere realization, with its source retained. -/
def sourceTriangleCone : SourceTriangleChain →ₗ[ℚ] SourceConedTriangleChain :=
  Finsupp.linearCombination ℚ fun base => Finsupp.single (coneOverTriangleMap base) 1

def sourceEdgeCone : SourceEdgeChain →ₗ[ℚ] SourceTriangleChain :=
  Finsupp.linearCombination ℚ fun edge => sourceTriangleGenerator (commonApexEdgeMap edge)

@[simp] theorem sourceConedTriangleBoundary_single
    (base : C(Tetrahedron, Triangle)) (coefficient : ℚ) :
    sourceConedTriangleBoundary (Finsupp.single base coefficient) =
      coefficient • ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
        sourceTriangleGenerator (base.comp (simplexFaceMap (degree := 2) face)) := by
  simp [sourceConedTriangleBoundary]

@[simp] theorem sourceTriangleCone_single (base : C(Triangle, Triangle)) (coefficient : ℚ) :
    sourceTriangleCone (Finsupp.single base coefficient) =
      coefficient • Finsupp.single (coneOverTriangleMap base) 1 := by
  simp [sourceTriangleCone]

@[simp] theorem sourceEdgeCone_single (edge : C(Segment, Triangle)) (coefficient : ℚ) :
    sourceEdgeCone (Finsupp.single edge coefficient) =
      coefficient • sourceTriangleGenerator (commonApexEdgeMap edge) := by
  simp [sourceEdgeCone]

/-- Exterior return and all three side faces, proved in the free source module. -/
theorem sourceConedTriangleBoundary_cone_affine (vertices : Fin 3 → Triangle) :
    sourceConedTriangleBoundary
        (sourceTriangleCone (sourceTriangleGenerator (triangleAffineMap vertices))) =
      sourceTriangleGenerator (triangleAffineMap vertices) -
        sourceEdgeCone (sourceBoundary (sourceTriangleGenerator (triangleAffineMap vertices))) := by
  classical
  have hfaceOne :
      (coneOverTriangleMap (triangleAffineMap vertices)).comp
          (simplexFaceMap (degree := 2) 1) =
        commonApexEdgeMap
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 0)) := by
    have hindex : (0 : Fin 3).succ = (1 : Fin 4) := by decide
    simpa only [hindex, coneOverTriangleFaceMap_eq_commonApexEdgeMap] using
      coneOverTriangleMap_face_succ (triangleAffineMap vertices) 0
  have hfaceTwo :
      (coneOverTriangleMap (triangleAffineMap vertices)).comp
          (simplexFaceMap (degree := 2) 2) =
        commonApexEdgeMap
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 1)) := by
    have hindex : (1 : Fin 3).succ = (2 : Fin 4) := by decide
    simpa only [hindex, coneOverTriangleFaceMap_eq_commonApexEdgeMap] using
      coneOverTriangleMap_face_succ (triangleAffineMap vertices) 1
  have hfaceThree :
      (coneOverTriangleMap (triangleAffineMap vertices)).comp
          (simplexFaceMap (degree := 2) 3) =
        commonApexEdgeMap
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 2)) := by
    have hindex : (2 : Fin 3).succ = (3 : Fin 4) := by decide
    simpa only [hindex, coneOverTriangleFaceMap_eq_commonApexEdgeMap] using
      coneOverTriangleMap_face_succ (triangleAffineMap vertices) 2
  simp only [sourceTriangleGenerator, sourceTriangleCone_single, one_smul,
    sourceConedTriangleBoundary_single, sourceBoundary_single, sourceTriangleBoundary]
  rw [Fin.sum_univ_four]
  repeat rw [Fin.sum_univ_three]
  rw [coneOverTriangleMap_face_zero_affine, hfaceOne, hfaceTwo, hfaceThree]
  simp only [map_add, map_smul, sourceEdgeGenerator, sourceEdgeCone_single,
    sourceTriangleGenerator, one_smul]
  norm_num
  module

theorem sourceConedTriangleBoundary_cone_barycentric (outerFace : Fin 3) (half : Fin 2) :
    sourceConedTriangleBoundary
        (sourceTriangleCone (sourceTriangleGenerator (barycentricTriangleMap outerFace half))) =
      sourceTriangleGenerator (barycentricTriangleMap outerFace half) -
        sourceEdgeCone (sourceBoundary
          (sourceTriangleGenerator (barycentricTriangleMap outerFace half))) :=
  sourceConedTriangleBoundary_cone_affine (barycentricTriangleVertices outerFace half)

theorem sourceConedTriangleBoundary_cone_id :
    sourceConedTriangleBoundary
        (sourceTriangleCone (sourceTriangleGenerator (ContinuousMap.id Triangle))) =
      sourceTriangleGenerator (ContinuousMap.id Triangle) -
        sourceEdgeCone (sourceBoundary (sourceTriangleGenerator (ContinuousMap.id Triangle))) := by
  simpa only [triangleAffineMap_canonicalVertices] using
    sourceConedTriangleBoundary_cone_affine (fun vertex : Fin 3 => stdSimplex.vertex vertex)

theorem sourceConedTriangleBoundary_cone_prism (outerFace : Fin 3) (kind : Fin 3) :
    sourceConedTriangleBoundary
        (sourceTriangleCone (sourceTriangleGenerator (residualPrismBase outerFace kind))) =
      sourceTriangleGenerator (residualPrismBase outerFace kind) -
        sourceEdgeCone (sourceBoundary
          (sourceTriangleGenerator (residualPrismBase outerFace kind))) := by
  rw [residualPrismBase_eq_triangleAffineMap_vertices]
  exact sourceConedTriangleBoundary_cone_affine _

/-- The complete sixteen-term free cone return.  No injectivity of a later receiver is used. -/
theorem sourceConedTriangleBoundary_sourceTriangleCone_residual :
    sourceConedTriangleBoundary (sourceTriangleCone sourceBarycentricResidual) =
      sourceBarycentricResidual := by
  classical
  have hreturn : sourceConedTriangleBoundary (sourceTriangleCone sourceBarycentricResidual) =
      sourceBarycentricResidual - sourceEdgeCone (sourceBoundary sourceBarycentricResidual) := by
    rw [sourceBarycentricResidual]
    simp only [map_sub, map_sum, map_smul]
    repeat rw [Fin.sum_univ_three]
    repeat rw [Fin.sum_univ_two]
    rw [sourceConedTriangleBoundary_cone_barycentric 0 0,
      sourceConedTriangleBoundary_cone_barycentric 0 1,
      sourceConedTriangleBoundary_cone_barycentric 1 0,
      sourceConedTriangleBoundary_cone_barycentric 1 1,
      sourceConedTriangleBoundary_cone_barycentric 2 0,
      sourceConedTriangleBoundary_cone_barycentric 2 1,
      sourceConedTriangleBoundary_cone_id,
      sourceConedTriangleBoundary_cone_prism 0 0,
      sourceConedTriangleBoundary_cone_prism 0 1,
      sourceConedTriangleBoundary_cone_prism 0 2,
      sourceConedTriangleBoundary_cone_prism 1 0,
      sourceConedTriangleBoundary_cone_prism 1 1,
      sourceConedTriangleBoundary_cone_prism 1 2,
      sourceConedTriangleBoundary_cone_prism 2 0,
      sourceConedTriangleBoundary_cone_prism 2 1,
      sourceConedTriangleBoundary_cone_prism 2 2]
    module
  rw [hreturn, sourceBoundary_sourceBarycentricResidual, map_zero, sub_zero]


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceConedTriangleBoundary_cone_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceConedTriangleBoundary_sourceTriangleCone_residual
