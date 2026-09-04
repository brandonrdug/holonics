import ElementaryHolonics.Millennium.HodgeBarycentricSubdivisionHomotopy

/-!
# The degree-two barycentric filling residual

The degree-one edge prism exposes the exact degree-two residual
`S₂ - id - ∂P₁`.  This file records the first source-faithful reduction of the filling problem:
the barycentric six-cell current should be compared with the already coned stellar current.  If
that comparison is proved, the existing stellar three-current is itself the required barycentric
filling.  No comparison is assumed here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricDegreeTwoFilling

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision
open Soma.Holonics.Millennium.HodgeStellarSubdivisionHomotopy
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricSubdivisionHomotopy

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

def barycentricResidual : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 2 :=
  barycentricTriangleSubdivisionMorphism - 𝟙 _ -
    SphereSingularChainComplex.d 2 1 ≫
      barycentricEdgeSubdivisionHomotopyMorphism

theorem barycentricResidual_comp_boundary :
    barycentricResidual ≫ SphereSingularChainComplex.d 2 1 = 0 := by
  rw [barycentricResidual,
    Preadditive.sub_comp, Preadditive.sub_comp,
    barycentricTriangleSubdivisionMorphism_comp_boundary,
    Category.id_comp, Category.assoc,
    barycentricEdgeSubdivisionHomotopyMorphism_comp_boundary,
    Preadditive.comp_sub, Category.comp_id]
  module

/-!
The tempting shortcut is to identify this residual with the existing stellar residual.  That
would require a new equality between the six barycentric source maps, the three stellar source
maps, and the nine edge-prism source maps.  Boundary equality alone is insufficient because the
singular chain basis retains each addressed source map.  The equality is therefore deliberately
left as the next seam obligation rather than asserted here.
-/

structure BarycentricDegreeTwoFilling where
  fill : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 3
  boundary : fill ≫ SphereSingularChainComplex.d 3 2 = barycentricResidual

/-!
The common-apex candidate below retains every source occurrence.  Its face-zero population is the
six barycentric triangles, the identity triangle, and the nine edge-prism triangles (sixteen
addressed affine terms in total).  The remaining faces are intentionally not silently discarded:
they are the seam table still required for an actual filling.
-/

def residualPrismBase (outerFace : Fin 3) (kind : Fin 3) : C(Triangle, Triangle) :=
  (simplexFaceMap (degree := 1) outerFace).comp
    (match kind with
    | 0 => edgeHomotopyMainMap
    | 1 => edgeHomotopyFoldMap
    | _ => edgeHomotopyConstantMap)

/-!
The common-apex constructor has an exact exterior-face law on the affine source maps.  The
qualification is essential: `coneOverTriangleMap base` samples an arbitrary continuous `base` at
its vertices, so it cannot recover a non-affine base map on the exterior face.
-/

theorem coneOverTriangleMap_face_zero_affine (vertices : Fin 3 → Triangle) :
    (coneOverTriangleMap (triangleAffineMap vertices)).comp
        (simplexFaceMap (degree := 2) 0) = triangleAffineMap vertices := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 0 point vertex *
      coneOverTriangleVertices (triangleAffineMap vertices) vertex coordinate) =
    ∑ vertex : Fin 3, point vertex * vertices vertex coordinate
  rw [Fin.sum_univ_three]
  fin_cases coordinate <;>
    simp [Fin.sum_univ_four, triangleAffineMap_apply,
      triangleAffineMap_vertex]

def commonApexResidualCone (simplex : SphereSingularSimplex 2) : SphereChain 3 :=
  (∑ outerFace : Fin 3, ∑ half : Fin 2,
      (-1 : ℚ) ^ ((outerFace : ℕ) + (half : ℕ)) •
        simplexGenerator
          (conedTriangleSubsimplex
            (barycentricTriangleMap outerFace half) simplex)) -
    simplexGenerator (conedTriangleSubsimplex (ContinuousMap.id Triangle) simplex) -
    ∑ outerFace : Fin 3, (-1 : ℚ) ^ (outerFace : ℕ) •
      (simplexGenerator
          (conedTriangleSubsimplex
            (residualPrismBase outerFace 0) simplex) -
        simplexGenerator
          (conedTriangleSubsimplex
            (residualPrismBase outerFace 1) simplex) -
        simplexGenerator
          (conedTriangleSubsimplex
            (residualPrismBase outerFace 2) simplex))

end Soma.Holonics.Millennium.HodgeBarycentricDegreeTwoFilling
