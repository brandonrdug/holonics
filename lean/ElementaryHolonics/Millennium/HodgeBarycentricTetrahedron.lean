import ElementaryHolonics.Millennium.HodgeBarycentricTriangleSubdivision
import ElementaryHolonics.Millennium.HodgeTetrahedralStellarSubdivision

/-!
# The twenty-four-cell barycentric refinement of a singular tetrahedron

An addressed descendant is the affine tetrahedron whose ordered vertices are the barycentres of
the nested flag

`tetrahedron ⊃ exterior face ⊃ edge ⊃ vertex`.

Thus its address is `Fin 4 × Fin 3 × Fin 2`, retaining all twenty-four occurrence lineages.  The
face opposite the tetrahedron barycentre is definitionally the checked six-cell barycentric
refinement of the addressed exterior triangle.  The exact rational contraction law supplies the
uniform degree-three mesh passage needed by the finite Hodge boundary carrier.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the imported simplex, affine-map, and degree-two
barycentric laws.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricTetrahedron

set_option maxHeartbeats 2000000

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision

/-- [definition] The ordered barycentres of one complete flag
`tetrahedron ⊃ face ⊃ edge ⊃ vertex`. -/
def barycentricTetrahedronVertices (outerFace : Fin 4) (innerFace : Fin 3)
    (half : Fin 2) : Fin 4 → Tetrahedron :=
  Fin.cases tetrahedronBarycenter fun faceVertex : Fin 3 =>
    simplexFaceMap (degree := 2) outerFace
      (barycentricTriangleVertices innerFace half faceVertex)

@[simp] theorem barycentricTetrahedronVertices_zero
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2) :
    barycentricTetrahedronVertices outerFace innerFace half 0 =
      tetrahedronBarycenter := rfl

@[simp] theorem barycentricTetrahedronVertices_succ
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2) (vertex : Fin 3) :
    barycentricTetrahedronVertices outerFace innerFace half vertex.succ =
      simplexFaceMap outerFace
        (barycentricTriangleVertices innerFace half vertex) := by
  rw [barycentricTetrahedronVertices, Fin.cases_succ]

@[simp] theorem barycentricTetrahedronVertices_one
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2) :
    barycentricTetrahedronVertices outerFace innerFace half 1 =
      simplexFaceMap outerFace
        (barycentricTriangleVertices innerFace half 0) := rfl

@[simp] theorem barycentricTetrahedronVertices_two
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2) :
    barycentricTetrahedronVertices outerFace innerFace half 2 =
      simplexFaceMap outerFace
        (barycentricTriangleVertices innerFace half 1) := rfl

@[simp] theorem barycentricTetrahedronVertices_three
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2) :
    barycentricTetrahedronVertices outerFace innerFace half 3 =
      simplexFaceMap outerFace
        (barycentricTriangleVertices innerFace half 2) := rfl

/-- [definition] One of the twenty-four exact affine source maps. -/
def barycentricTetrahedronMap (outerFace : Fin 4) (innerFace : Fin 3)
    (half : Fin 2) : C(Tetrahedron, Tetrahedron) :=
  tetrahedronAffineMap
    (barycentricTetrahedronVertices outerFace innerFace half)

/-- [proved-derived; formal-checked] Deleting the tetrahedron barycentre returns exactly the
addressed six-cell barycentric triangle map on the selected exterior face. -/
theorem barycentricTetrahedronMap_face_zero
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2) :
    (barycentricTetrahedronMap outerFace innerFace half).comp
        (simplexFaceMap (degree := 2) 0) =
      (simplexFaceMap (degree := 2) outerFace).comp
        (barycentricTriangleMap innerFace half) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4,
      simplexFaceMap (degree := 2) 0 point vertex *
        barycentricTetrahedronVertices outerFace innerFace half vertex coordinate) =
    simplexFaceMap (degree := 2) outerFace
      (barycentricTriangleMap innerFace half point) coordinate
  fin_cases outerFace <;> fin_cases innerFace <;> fin_cases half <;>
    fin_cases coordinate <;>
    simp [barycentricTriangleMap, triangleAffineMap_apply,
      Fin.sum_univ_four, Fin.sum_univ_three, Fin.succAbove]

/-- [proved-derived; formal-checked] The two flags differing only in their final half-edge share
the face obtained by deleting the retained original vertex. -/
theorem barycentricTetrahedronMap_half_pair (outerFace : Fin 4) (innerFace : Fin 3) :
    (barycentricTetrahedronMap outerFace innerFace 0).comp
        (simplexFaceMap (degree := 2) 3) =
      (barycentricTetrahedronMap outerFace innerFace 1).comp
        (simplexFaceMap (degree := 2) 3) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 3 point vertex *
      barycentricTetrahedronVertices outerFace innerFace 0 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 3 point vertex *
      barycentricTetrahedronVertices outerFace innerFace 1 vertex coordinate
  fin_cases outerFace <;> fin_cases innerFace <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] First radial face pairing inside every exterior face. -/
theorem barycentricTetrahedronMap_radial_two (outerFace : Fin 4) :
    (barycentricTetrahedronMap outerFace 0 0).comp
        (simplexFaceMap (degree := 2) 2) =
      (barycentricTetrahedronMap outerFace 1 0).comp
        (simplexFaceMap (degree := 2) 2) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      barycentricTetrahedronVertices outerFace 0 0 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      barycentricTetrahedronVertices outerFace 1 0 vertex coordinate
  fin_cases outerFace <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Second radial face pairing inside every exterior face. -/
theorem barycentricTetrahedronMap_radial_one (outerFace : Fin 4) :
    (barycentricTetrahedronMap outerFace 0 1).comp
        (simplexFaceMap (degree := 2) 2) =
      (barycentricTetrahedronMap outerFace 2 0).comp
        (simplexFaceMap (degree := 2) 2) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      barycentricTetrahedronVertices outerFace 0 1 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      barycentricTetrahedronVertices outerFace 2 0 vertex coordinate
  fin_cases outerFace <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Third radial face pairing inside every exterior face. -/
theorem barycentricTetrahedronMap_radial_zero (outerFace : Fin 4) :
    (barycentricTetrahedronMap outerFace 1 1).comp
        (simplexFaceMap (degree := 2) 2) =
      (barycentricTetrahedronMap outerFace 2 1).comp
        (simplexFaceMap (degree := 2) 2) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      barycentricTetrahedronVertices outerFace 1 1 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      barycentricTetrahedronVertices outerFace 2 1 vertex coordinate
  fin_cases outerFace <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Paired refinements on the common face of outer cones `0,1`. -/
theorem barycentricTetrahedronMap_outer_01 (half : Fin 2) :
    (barycentricTetrahedronMap 0 0 half).comp (simplexFaceMap (degree := 2) 1) =
      (barycentricTetrahedronMap 1 0 half).comp
        (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 0 0 half vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 1 0 half vertex coordinate
  fin_cases half <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Paired refinements on the common face of outer cones `0,2`. -/
theorem barycentricTetrahedronMap_outer_02 (half : Fin 2) :
    (barycentricTetrahedronMap 0 1 half).comp (simplexFaceMap (degree := 2) 1) =
      (barycentricTetrahedronMap 2 0 half).comp
        (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 0 1 half vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 2 0 half vertex coordinate
  fin_cases half <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Paired refinements on the common face of outer cones `0,3`. -/
theorem barycentricTetrahedronMap_outer_03 (half : Fin 2) :
    (barycentricTetrahedronMap 0 2 half).comp (simplexFaceMap (degree := 2) 1) =
      (barycentricTetrahedronMap 3 0 half).comp
        (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 0 2 half vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 3 0 half vertex coordinate
  fin_cases half <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Paired refinements on the common face of outer cones `1,2`. -/
theorem barycentricTetrahedronMap_outer_12 (half : Fin 2) :
    (barycentricTetrahedronMap 1 1 half).comp (simplexFaceMap (degree := 2) 1) =
      (barycentricTetrahedronMap 2 1 half).comp
        (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 1 1 half vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 2 1 half vertex coordinate
  fin_cases half <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Paired refinements on the common face of outer cones `1,3`. -/
theorem barycentricTetrahedronMap_outer_13 (half : Fin 2) :
    (barycentricTetrahedronMap 1 2 half).comp (simplexFaceMap (degree := 2) 1) =
      (barycentricTetrahedronMap 3 1 half).comp
        (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 1 2 half vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 3 1 half vertex coordinate
  fin_cases half <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [proved-derived; formal-checked] Paired refinements on the common face of outer cones `2,3`. -/
theorem barycentricTetrahedronMap_outer_23 (half : Fin 2) :
    (barycentricTetrahedronMap 2 2 half).comp (simplexFaceMap (degree := 2) 1) =
      (barycentricTetrahedronMap 3 2 half).comp
        (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 2 2 half vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      barycentricTetrahedronVertices 3 2 half vertex coordinate
  fin_cases half <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

/-- [definition] One addressed geometric subtetrahedron of a singular three-simplex. -/
def barycentricTetrahedronSubsimplex (outerFace : Fin 4) (innerFace : Fin 3)
    (half : Fin 2) (simplex : SphereSingularSimplex 3) : SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 3)) simplex).comp
          (barycentricTetrahedronMap outerFace innerFace half))

/-- [proved-derived; formal-checked] The exterior singular face is exactly the corresponding
degree-two barycentric descendant. -/
theorem barycentricTetrahedronSubsimplex_face_zero
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2)
    (simplex : SphereSingularSimplex 3) :
    simplexFace 0
        (barycentricTetrahedronSubsimplex outerFace innerFace half simplex) =
      barycentricTriangleSubsimplex innerFace half
        (simplexFace outerFace simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [barycentricTetrahedronSubsimplex, Equiv.apply_symm_apply]
  rw [barycentricTriangleSubsimplex]
  simp only [Equiv.apply_symm_apply]
  rw [simplexFace_realization, ContinuousMap.comp_assoc,
    barycentricTetrahedronMap_face_zero, ← ContinuousMap.comp_assoc]

/-- A source-map seam equality transports through every singular three-simplex. -/
theorem barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    (leftOuter rightOuter : Fin 4) (leftInner rightInner : Fin 3)
    (leftHalf rightHalf : Fin 2) (leftFace rightFace : Fin 4)
    (mapEq :
      (barycentricTetrahedronMap leftOuter leftInner leftHalf).comp
          (simplexFaceMap (degree := 2) leftFace) =
        (barycentricTetrahedronMap rightOuter rightInner rightHalf).comp
          (simplexFaceMap (degree := 2) rightFace))
    (simplex : SphereSingularSimplex 3) :
    simplexFace leftFace
        (barycentricTetrahedronSubsimplex leftOuter leftInner leftHalf simplex) =
      simplexFace rightFace
        (barycentricTetrahedronSubsimplex rightOuter rightInner rightHalf simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [barycentricTetrahedronSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, mapEq]

theorem barycentricTetrahedronSubsimplex_half_pair
    (outerFace : Fin 4) (innerFace : Fin 3) (simplex : SphereSingularSimplex 3) :
    simplexFace 3
        (barycentricTetrahedronSubsimplex outerFace innerFace 0 simplex) =
      simplexFace 3
        (barycentricTetrahedronSubsimplex outerFace innerFace 1 simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    outerFace outerFace innerFace innerFace 0 1 3 3
    (barycentricTetrahedronMap_half_pair outerFace innerFace) simplex

theorem barycentricTetrahedronSubsimplex_radial_two
    (outerFace : Fin 4) (simplex : SphereSingularSimplex 3) :
    simplexFace 2 (barycentricTetrahedronSubsimplex outerFace 0 0 simplex) =
      simplexFace 2
        (barycentricTetrahedronSubsimplex outerFace 1 0 simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    outerFace outerFace 0 1 0 0 2 2
    (barycentricTetrahedronMap_radial_two outerFace) simplex

theorem barycentricTetrahedronSubsimplex_radial_one
    (outerFace : Fin 4) (simplex : SphereSingularSimplex 3) :
    simplexFace 2 (barycentricTetrahedronSubsimplex outerFace 0 1 simplex) =
      simplexFace 2
        (barycentricTetrahedronSubsimplex outerFace 2 0 simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    outerFace outerFace 0 2 1 0 2 2
    (barycentricTetrahedronMap_radial_one outerFace) simplex

theorem barycentricTetrahedronSubsimplex_radial_zero
    (outerFace : Fin 4) (simplex : SphereSingularSimplex 3) :
    simplexFace 2 (barycentricTetrahedronSubsimplex outerFace 1 1 simplex) =
      simplexFace 2
        (barycentricTetrahedronSubsimplex outerFace 2 1 simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    outerFace outerFace 1 2 1 1 2 2
    (barycentricTetrahedronMap_radial_zero outerFace) simplex

theorem barycentricTetrahedronSubsimplex_outer_01
    (half : Fin 2) (simplex : SphereSingularSimplex 3) :
    simplexFace 1 (barycentricTetrahedronSubsimplex 0 0 half simplex) =
      simplexFace 1 (barycentricTetrahedronSubsimplex 1 0 half simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    0 1 0 0 half half 1 1 (barycentricTetrahedronMap_outer_01 half) simplex

theorem barycentricTetrahedronSubsimplex_outer_02
    (half : Fin 2) (simplex : SphereSingularSimplex 3) :
    simplexFace 1 (barycentricTetrahedronSubsimplex 0 1 half simplex) =
      simplexFace 1 (barycentricTetrahedronSubsimplex 2 0 half simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    0 2 1 0 half half 1 1 (barycentricTetrahedronMap_outer_02 half) simplex

theorem barycentricTetrahedronSubsimplex_outer_03
    (half : Fin 2) (simplex : SphereSingularSimplex 3) :
    simplexFace 1 (barycentricTetrahedronSubsimplex 0 2 half simplex) =
      simplexFace 1 (barycentricTetrahedronSubsimplex 3 0 half simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    0 3 2 0 half half 1 1 (barycentricTetrahedronMap_outer_03 half) simplex

theorem barycentricTetrahedronSubsimplex_outer_12
    (half : Fin 2) (simplex : SphereSingularSimplex 3) :
    simplexFace 1 (barycentricTetrahedronSubsimplex 1 1 half simplex) =
      simplexFace 1 (barycentricTetrahedronSubsimplex 2 1 half simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    1 2 1 1 half half 1 1 (barycentricTetrahedronMap_outer_12 half) simplex

theorem barycentricTetrahedronSubsimplex_outer_13
    (half : Fin 2) (simplex : SphereSingularSimplex 3) :
    simplexFace 1 (barycentricTetrahedronSubsimplex 1 2 half simplex) =
      simplexFace 1 (barycentricTetrahedronSubsimplex 3 1 half simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    1 3 2 1 half half 1 1 (barycentricTetrahedronMap_outer_13 half) simplex

theorem barycentricTetrahedronSubsimplex_outer_23
    (half : Fin 2) (simplex : SphereSingularSimplex 3) :
    simplexFace 1 (barycentricTetrahedronSubsimplex 2 2 half simplex) =
      simplexFace 1 (barycentricTetrahedronSubsimplex 3 2 half simplex) :=
  barycentricTetrahedronSubsimplex_face_eq_of_map_face_eq
    2 3 2 2 half half 1 1 (barycentricTetrahedronMap_outer_23 half) simplex

/-- [definition] The signed twenty-four-cell occurrence population.  Its unproved next law is the
complete internal-seam cancellation returning the existing barycentric triangle subdivision of
the original boundary. -/
def barycentricTetrahedronSubdivision (simplex : SphereSingularSimplex 3) : SphereChain 3 :=
  ∑ outerFace : Fin 4, ∑ innerFace : Fin 3, ∑ half : Fin 2,
    (-1 : ℚ) ^ ((outerFace : ℕ) + (innerFace : ℕ) + (half : ℕ)) •
      simplexGenerator
        (barycentricTetrahedronSubsimplex outerFace innerFace half simplex)

/-- [definition] The existing six-cell barycentric triangle current applied with the original
tetrahedral boundary signs. -/
def barycentricallySubdividedTetrahedronBoundary
    (simplex : SphereSingularSimplex 3) : SphereChain 2 :=
  ∑ outerFace : Fin 4, (-1 : ℚ) ^ (outerFace : ℕ) •
    barycentricTriangleSubdivision (simplexFace outerFace simplex)

/-- [proved-derived; formal-checked] **TWENTY-FOUR-CELL SEAM LAW.**  All thirty-six internal
triangular faces cancel in oppositely signed pairs, while the twenty-four exterior faces return
exactly the six-cell barycentric subdivision of each original boundary face. -/
theorem boundary_barycentricTetrahedronSubdivision
    (simplex : SphereSingularSimplex 3) :
    SphereSingularChainComplex.d 3 2
        (barycentricTetrahedronSubdivision simplex) =
      barycentricallySubdividedTetrahedronBoundary simplex := by
  rw [barycentricTetrahedronSubdivision, map_sum]
  simp only [map_sum, map_smul, boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_four]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  repeat rw [Fin.sum_univ_four]
  simp_rw [barycentricTetrahedronSubsimplex_face_zero]
  simp_rw [barycentricTetrahedronSubsimplex_half_pair]
  simp_rw [barycentricTetrahedronSubsimplex_radial_two,
    barycentricTetrahedronSubsimplex_radial_one,
    barycentricTetrahedronSubsimplex_radial_zero]
  simp_rw [barycentricTetrahedronSubsimplex_outer_01,
    barycentricTetrahedronSubsimplex_outer_02,
    barycentricTetrahedronSubsimplex_outer_03,
    barycentricTetrahedronSubsimplex_outer_12,
    barycentricTetrahedronSubsimplex_outer_13,
    barycentricTetrahedronSubsimplex_outer_23]
  rw [barycentricallySubdividedTetrahedronBoundary]
  repeat rw [Fin.sum_univ_four]
  simp only [barycentricTriangleSubdivision]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  norm_num
  module

def barycentricTetrahedronCoefficient
    (value : SphereSingularChainComplex.X 3) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 3 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • value
      map_add' := fun left right => add_smul left right value
      map_smul' := by
        intro scalar coefficient
        exact (smul_smul scalar coefficient value).symm }

/-- [definition] Linear extension of the twenty-four-cell subdivision to every rational singular
three-chain. -/
def barycentricTetrahedronSubdivisionMorphism :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 3 :=
  Limits.Sigma.desc fun simplex =>
    barycentricTetrahedronCoefficient (barycentricTetrahedronSubdivision simplex)

@[simp]
theorem barycentricTetrahedronSubdivisionMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 3) :
    barycentricTetrahedronSubdivisionMorphism (simplexGenerator simplex) =
      barycentricTetrahedronSubdivision simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source =>
          barycentricTetrahedronCoefficient (barycentricTetrahedronSubdivision source)))
      (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

theorem barycentricallySubdividedTetrahedronBoundary_eq_morphism_boundary
    (simplex : SphereSingularSimplex 3) :
    barycentricallySubdividedTetrahedronBoundary simplex =
      barycentricTriangleSubdivisionMorphism
        (SphereSingularChainComplex.d 3 2 (simplexGenerator simplex)) := by
  rw [boundary_simplexGenerator, map_sum,
    barycentricallySubdividedTetrahedronBoundary]
  apply Finset.sum_congr rfl
  intro outerFace _
  rw [map_smul, barycentricTriangleSubdivisionMorphism_simplexGenerator]

/-- [proved-derived; formal-checked] **BARYCENTRIC DEGREE-THREE CHAIN SQUARE.**  The new
degree-three refinement and the existing degree-two refinement commute exactly with boundary. -/
theorem barycentricTetrahedronSubdivisionMorphism_comp_boundary :
    barycentricTetrahedronSubdivisionMorphism ≫
        SphereSingularChainComplex.d 3 2 =
      SphereSingularChainComplex.d 3 2 ≫
        barycentricTriangleSubdivisionMorphism := by
  let left : SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 2 :=
    barycentricTetrahedronSubdivisionMorphism ≫ SphereSingularChainComplex.d 3 2
  let right : SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 2 :=
    SphereSingularChainComplex.d 3 2 ≫ barycentricTriangleSubdivisionMorphism
  have hleftRight : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change ℚ at coefficient
    simp only [left, right]
    change SphereSingularChainComplex.d 3 2
        (barycentricTetrahedronSubdivisionMorphism
          ((Limits.Sigma.ι
            (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex) coefficient)) =
      barycentricTriangleSubdivisionMorphism
        (SphereSingularChainComplex.d 3 2
          ((Limits.Sigma.ι
            (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex) coefficient))
    rw [Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
    change SphereSingularChainComplex.d 3 2
        (barycentricTetrahedronSubdivisionMorphism
          (coefficient • simplexGenerator simplex)) =
      barycentricTriangleSubdivisionMorphism
        (SphereSingularChainComplex.d 3 2
          (coefficient • simplexGenerator simplex))
    simp only [map_smul,
      barycentricTetrahedronSubdivisionMorphism_simplexGenerator,
      boundary_barycentricTetrahedronSubdivision,
      barycentricallySubdividedTetrahedronBoundary_eq_morphism_boundary]
  exact hleftRight

theorem boundary_barycentricTetrahedronSubdivisionMorphism
    (chain : SphereChain 3) :
    SphereSingularChainComplex.d 3 2
        (barycentricTetrahedronSubdivisionMorphism chain) =
      barycentricTriangleSubdivisionMorphism
        (SphereSingularChainComplex.d 3 2 chain) := by
  simpa only [ConcreteCategory.comp_apply] using
    congrArg (fun morphism : SphereSingularChainComplex.X 3 ⟶
      SphereSingularChainComplex.X 2 => morphism chain)
      barycentricTetrahedronSubdivisionMorphism_comp_boundary

/-- [definition] Repeated degree-three barycentric refinement. -/
def iteratedBarycentricTetrahedronSubdivision : ℕ → SphereChain 3 → SphereChain 3
  | 0 => id
  | scale + 1 => fun chain =>
      barycentricTetrahedronSubdivisionMorphism
        (iteratedBarycentricTetrahedronSubdivision scale chain)

/-- [definition] The matching repeated degree-two barycentric refinement. -/
def iteratedBarycentricTriangleSubdivision : ℕ → SphereChain 2 → SphereChain 2
  | 0 => id
  | scale + 1 => fun chain =>
      barycentricTriangleSubdivisionMorphism
        (iteratedBarycentricTriangleSubdivision scale chain)

/-- [proved-derived; formal-checked] Every finite degree-three refinement depth returns exactly
the matching degree-two refinement of the original boundary. -/
theorem boundary_iteratedBarycentricTetrahedronSubdivision
    (scale : ℕ) (chain : SphereChain 3) :
    SphereSingularChainComplex.d 3 2
        (iteratedBarycentricTetrahedronSubdivision scale chain) =
      iteratedBarycentricTriangleSubdivision scale
        (SphereSingularChainComplex.d 3 2 chain) := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      rw [iteratedBarycentricTetrahedronSubdivision,
        boundary_barycentricTetrahedronSubdivisionMorphism,
        inductionHypothesis, iteratedBarycentricTriangleSubdivision]

/-- [definition] Exact squared coordinate distance on the standard tetrahedron. -/
def tetrahedronSquaredCoordinateDistance (left right : Tetrahedron) : ℝ :=
  ∑ coordinate : Fin 4, (left coordinate - right coordinate) ^ 2

theorem tetrahedronSquaredCoordinateDistance_nonneg (left right : Tetrahedron) :
    0 ≤ tetrahedronSquaredCoordinateDistance left right := by
  exact Finset.sum_nonneg fun coordinate _ => sq_nonneg _

/-- [proved-derived; formal-checked] Exact quadratic certificate for the four-stage flag map.
The proof is a rational sum-of-squares certificate; no numerical approximation occurs. -/
theorem barycentricTetrahedronQuadratic_contraction
    (a b c d : ℝ) (sumZero : a + b + c + d = 0) :
    (a / 4) ^ 2 + (a / 4 + b / 3) ^ 2 +
        (a / 4 + b / 3 + c / 2) ^ 2 +
        (a / 4 + b / 3 + c / 2 + d) ^ 2 ≤
      ((9 : ℝ) / 16) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have hd : d = -a - b - c := by linarith
  rw [hd]
  nlinarith [
    sq_nonneg (a - (5 / 18 : ℝ) * b + (1 / 6 : ℝ) * c),
    sq_nonneg (b + (69 / 371 : ℝ) * c),
    sq_nonneg c]

/-- [proved-derived; formal-checked] Every one of the twenty-four flag maps contracts exact
squared coordinate distance by the uniform rational factor `9/16`. -/
theorem tetrahedronSquaredCoordinateDistance_barycentricTetrahedronMap
    (outerFace : Fin 4) (innerFace : Fin 3) (half : Fin 2)
    (left right : Tetrahedron) :
    tetrahedronSquaredCoordinateDistance
        (barycentricTetrahedronMap outerFace innerFace half left)
        (barycentricTetrahedronMap outerFace innerFace half right) ≤
      ((9 : ℝ) / 16) * tetrahedronSquaredCoordinateDistance left right := by
  have hleft := stdSimplex.sum_eq_one left
  have hright := stdSimplex.sum_eq_one right
  rw [Fin.sum_univ_four] at hleft hright
  fin_cases outerFace <;> fin_cases innerFace <;> fin_cases half <;>
    simp only [tetrahedronSquaredCoordinateDistance, barycentricTetrahedronMap,
      tetrahedronAffineMap_apply, Fin.sum_univ_four] <;>
    simp [barycentricTetrahedronVertices_zero,
      barycentricTetrahedronVertices_one,
      barycentricTetrahedronVertices_two,
      barycentricTetrahedronVertices_three,
      barycentricTriangleVertices_zero, barycentricTriangleVertices_one,
      barycentricTriangleVertices_two, Fin.succAbove]
  all_goals
    have sumZero :
        (left 0 - right 0) + (left 1 - right 1) +
          (left 2 - right 2) + (left 3 - right 3) = 0 := by
      linarith
    have contract := barycentricTetrahedronQuadratic_contraction
      (left 0 - right 0) (left 1 - right 1)
      (left 2 - right 2) (left 3 - right 3) sumZero
    norm_num at contract ⊢
    nlinarith [contract]

/-- [definition] Complete lineage address of one of the twenty-four descendants. -/
abbrev BarycentricTetrahedronAddress := Fin 4 × Fin 3 × Fin 2

/-- [definition] Complete source map of an addressed degree-three descendant word. -/
def barycentricTetrahedronWordMap :
    List BarycentricTetrahedronAddress → C(Tetrahedron, Tetrahedron)
  | [] => ContinuousMap.id Tetrahedron
  | address :: tail =>
      (barycentricTetrahedronWordMap tail).comp
        (barycentricTetrahedronMap address.1 address.2.1 address.2.2)

/-- [proved-derived; formal-checked] Address concatenation is literal serial composition. -/
theorem barycentricTetrahedronWordMap_append
    (first second : List BarycentricTetrahedronAddress) :
    barycentricTetrahedronWordMap (first ++ second) =
      (barycentricTetrahedronWordMap second).comp
        (barycentricTetrahedronWordMap first) := by
  induction first with
  | nil =>
      apply ContinuousMap.ext
      intro point
      rfl
  | cons address tail inductionHypothesis =>
      simp only [List.cons_append, barycentricTetrahedronWordMap,
        inductionHypothesis, ContinuousMap.comp_assoc]

/-- [proved-derived; formal-checked] Every degree-three descendant word contracts by the exact
power `(9/16)^word.length`. -/
theorem tetrahedronSquaredCoordinateDistance_barycentricTetrahedronWordMap
    (word : List BarycentricTetrahedronAddress) (left right : Tetrahedron) :
    tetrahedronSquaredCoordinateDistance
        (barycentricTetrahedronWordMap word left)
        (barycentricTetrahedronWordMap word right) ≤
      ((9 : ℝ) / 16) ^ word.length *
        tetrahedronSquaredCoordinateDistance left right := by
  induction word generalizing left right with
  | nil =>
      simp [barycentricTetrahedronWordMap]
  | cons address tail inductionHypothesis =>
      rw [barycentricTetrahedronWordMap, ContinuousMap.comp_apply]
      calc
        tetrahedronSquaredCoordinateDistance
            (barycentricTetrahedronWordMap tail
              (barycentricTetrahedronMap
                address.1 address.2.1 address.2.2 left))
            (barycentricTetrahedronWordMap tail
              (barycentricTetrahedronMap
                address.1 address.2.1 address.2.2 right)) ≤
            ((9 : ℝ) / 16) ^ tail.length *
              tetrahedronSquaredCoordinateDistance
                (barycentricTetrahedronMap
                  address.1 address.2.1 address.2.2 left)
                (barycentricTetrahedronMap
                  address.1 address.2.1 address.2.2 right) :=
          inductionHypothesis _ _
        _ ≤ ((9 : ℝ) / 16) ^ tail.length *
              (((9 : ℝ) / 16) *
                tetrahedronSquaredCoordinateDistance left right) := by
          exact mul_le_mul_of_nonneg_left
            (tetrahedronSquaredCoordinateDistance_barycentricTetrahedronMap
              address.1 address.2.1 address.2.2 left right) (by positivity)
        _ = ((9 : ℝ) / 16) ^ (address :: tail).length *
              tetrahedronSquaredCoordinateDistance left right := by
          simp only [List.length_cons, pow_succ]
          ring

section Audit

#print axioms barycentricTetrahedronMap_face_zero
#print axioms barycentricTetrahedronSubsimplex_face_zero
#print axioms boundary_barycentricTetrahedronSubdivision
#print axioms barycentricTetrahedronSubdivisionMorphism_comp_boundary
#print axioms boundary_iteratedBarycentricTetrahedronSubdivision
#print axioms barycentricTetrahedronQuadratic_contraction
#print axioms tetrahedronSquaredCoordinateDistance_barycentricTetrahedronMap
#print axioms barycentricTetrahedronWordMap_append
#print axioms tetrahedronSquaredCoordinateDistance_barycentricTetrahedronWordMap

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricTetrahedron
