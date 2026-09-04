import ElementaryHolonics.Millennium.HodgeBarycentricEdgeSubdivision

/-!
# The six-cell barycentric subdivision of a singular triangle

Cone the checked two-half subdivision of each addressed boundary edge to the triangle barycentre.
The result has six geometric subtriangles.  Three midpoint seams and three vertex-radial seams
cancel in oppositely oriented pairs; the exterior returns the barycentrically subdivided boundary.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision

/-- The ordered vertices `[triangle barycentre, edge midpoint, retained edge endpoint]`. -/
def barycentricTriangleVertices (outerFace : Fin 3) (half : Fin 2) :
    Fin 3 → Triangle :=
  Fin.cases triangleBarycenter fun edgeVertex : Fin 2 =>
    simplexFaceMap (degree := 1) outerFace
      (edgeConeMap half (stdSimplex.vertex edgeVertex))

@[simp] theorem barycentricTriangleVertices_zero (outerFace : Fin 3) (half : Fin 2) :
    barycentricTriangleVertices outerFace half 0 = triangleBarycenter := rfl

@[simp] theorem barycentricTriangleVertices_one (outerFace : Fin 3) (half : Fin 2) :
    barycentricTriangleVertices outerFace half 1 =
      simplexFaceMap (degree := 1) outerFace segmentMidpoint := by
  change simplexFaceMap (degree := 1) outerFace
      (edgeConeMap half (stdSimplex.vertex 0)) =
    simplexFaceMap (degree := 1) outerFace segmentMidpoint
  rw [edgeConeMap_vertex_zero]

@[simp] theorem barycentricTriangleVertices_two (outerFace : Fin 3) (half : Fin 2) :
    barycentricTriangleVertices outerFace half 2 =
      stdSimplex.vertex (outerFace.succAbove (half.succAbove 0)) := by
  change simplexFaceMap (degree := 1) outerFace
      (edgeConeMap half (stdSimplex.vertex 1)) =
    stdSimplex.vertex (outerFace.succAbove (half.succAbove 0))
  rw [edgeConeMap_vertex_one]
  apply stdSimplex.ext
  funext coordinate
  fin_cases outerFace <;> fin_cases half <;> fin_cases coordinate <;>
    simp [Fin.succAbove]

def barycentricTriangleMap (outerFace : Fin 3) (half : Fin 2) :
    C(Triangle, Triangle) :=
  triangleAffineMap (barycentricTriangleVertices outerFace half)

/-- The exterior face is exactly the selected half of the selected original edge. -/
theorem barycentricTriangleMap_face_zero (outerFace : Fin 3) (half : Fin 2) :
    (barycentricTriangleMap outerFace half).comp
        (simplexFaceMap (degree := 1) 0) =
      (simplexFaceMap (degree := 1) outerFace).comp (edgeConeMap half) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 0 point vertex *
        barycentricTriangleVertices outerFace half vertex coordinate) =
    simplexFaceMap (degree := 1) outerFace (edgeConeMap half point) coordinate
  fin_cases outerFace <;> fin_cases half <;> fin_cases coordinate <;>
    simp [edgeConeMap, Fin.sum_univ_three, Fin.sum_univ_two, Fin.succAbove]

/-- The two halves of one exterior edge share the cone-to-midpoint seam. -/
theorem barycentricTriangleMap_midpoint_pair (outerFace : Fin 3) :
    (barycentricTriangleMap outerFace 0).comp
        (simplexFaceMap (degree := 1) 2) =
      (barycentricTriangleMap outerFace 1).comp
        (simplexFaceMap (degree := 1) 2) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 2 point vertex *
        barycentricTriangleVertices outerFace 0 vertex coordinate) =
    ∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 2 point vertex *
        barycentricTriangleVertices outerFace 1 vertex coordinate
  fin_cases outerFace <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_three, Fin.succAbove]

/-- The radial seam from the barycentre to original vertex `2`. -/
theorem barycentricTriangleMap_radial_two :
    (barycentricTriangleMap 0 0).comp (simplexFaceMap (degree := 1) 1) =
      (barycentricTriangleMap 1 0).comp (simplexFaceMap (degree := 1) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3, simplexFaceMap (degree := 1) 1 point vertex *
      barycentricTriangleVertices 0 0 vertex coordinate) =
    ∑ vertex : Fin 3, simplexFaceMap (degree := 1) 1 point vertex *
      barycentricTriangleVertices 1 0 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_three, Fin.succAbove]

/-- The radial seam from the barycentre to original vertex `1`. -/
theorem barycentricTriangleMap_radial_one :
    (barycentricTriangleMap 0 1).comp (simplexFaceMap (degree := 1) 1) =
      (barycentricTriangleMap 2 0).comp (simplexFaceMap (degree := 1) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3, simplexFaceMap (degree := 1) 1 point vertex *
      barycentricTriangleVertices 0 1 vertex coordinate) =
    ∑ vertex : Fin 3, simplexFaceMap (degree := 1) 1 point vertex *
      barycentricTriangleVertices 2 0 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_three, Fin.succAbove]

/-- The radial seam from the barycentre to original vertex `0`. -/
theorem barycentricTriangleMap_radial_zero :
    (barycentricTriangleMap 1 1).comp (simplexFaceMap (degree := 1) 1) =
      (barycentricTriangleMap 2 1).comp (simplexFaceMap (degree := 1) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3, simplexFaceMap (degree := 1) 1 point vertex *
      barycentricTriangleVertices 1 1 vertex coordinate) =
    ∑ vertex : Fin 3, simplexFaceMap (degree := 1) 1 point vertex *
      barycentricTriangleVertices 2 1 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_three, Fin.succAbove]

/-- One of the six barycentric subsimplices of a singular triangle. -/
def barycentricTriangleSubsimplex (outerFace : Fin 3) (half : Fin 2)
    (simplex : SphereSingularSimplex 2) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2)) simplex).comp
          (barycentricTriangleMap outerFace half))

theorem barycentricTriangleSubsimplex_face_zero (outerFace : Fin 3) (half : Fin 2)
    (simplex : SphereSingularSimplex 2) :
    simplexFace 0 (barycentricTriangleSubsimplex outerFace half simplex) =
      barycentricEdgeSubsimplex half (simplexFace outerFace simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization]
  simp only [barycentricTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [barycentricEdgeSubsimplex]
  simp only [Equiv.apply_symm_apply]
  rw [simplexFace_realization, ContinuousMap.comp_assoc,
    barycentricTriangleMap_face_zero, ← ContinuousMap.comp_assoc]

theorem barycentricTriangleSubsimplex_midpoint_pair (outerFace : Fin 3)
    (simplex : SphereSingularSimplex 2) :
    simplexFace 2 (barycentricTriangleSubsimplex outerFace 0 simplex) =
      simplexFace 2 (barycentricTriangleSubsimplex outerFace 1 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [barycentricTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
    barycentricTriangleMap_midpoint_pair]

theorem barycentricTriangleSubsimplex_radial_two (simplex : SphereSingularSimplex 2) :
    simplexFace 1 (barycentricTriangleSubsimplex 0 0 simplex) =
      simplexFace 1 (barycentricTriangleSubsimplex 1 0 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [barycentricTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
    barycentricTriangleMap_radial_two]

theorem barycentricTriangleSubsimplex_radial_one (simplex : SphereSingularSimplex 2) :
    simplexFace 1 (barycentricTriangleSubsimplex 0 1 simplex) =
      simplexFace 1 (barycentricTriangleSubsimplex 2 0 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [barycentricTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
    barycentricTriangleMap_radial_one]

theorem barycentricTriangleSubsimplex_radial_zero (simplex : SphereSingularSimplex 2) :
    simplexFace 1 (barycentricTriangleSubsimplex 1 1 simplex) =
      simplexFace 1 (barycentricTriangleSubsimplex 2 1 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [barycentricTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
    barycentricTriangleMap_radial_zero]

/-- The signed six-cell barycentric subdivision of one singular triangle. -/
def barycentricTriangleSubdivision (simplex : SphereSingularSimplex 2) : SphereChain 2 :=
  ∑ outerFace : Fin 3, ∑ half : Fin 2,
    (-1 : ℚ) ^ ((outerFace : ℕ) + (half : ℕ)) •
      simplexGenerator (barycentricTriangleSubsimplex outerFace half simplex)

/-- The exact edge-refined boundary returned by the six-cell subdivision. -/
def barycentricallySubdividedBoundary (simplex : SphereSingularSimplex 2) : SphereChain 1 :=
  ∑ outerFace : Fin 3, (-1 : ℚ) ^ (outerFace : ℕ) •
    barycentricEdgeSubdivision (simplexFace outerFace simplex)

theorem boundary_barycentricTriangleSubdivision (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 2 1 (barycentricTriangleSubdivision simplex) =
      barycentricallySubdividedBoundary simplex := by
  rw [barycentricTriangleSubdivision, map_sum]
  simp only [map_sum, map_smul, boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  repeat rw [Fin.sum_univ_three]
  rw [barycentricTriangleSubsimplex_face_zero 0 0,
    barycentricTriangleSubsimplex_face_zero 0 1,
    barycentricTriangleSubsimplex_face_zero 1 0,
    barycentricTriangleSubsimplex_face_zero 1 1,
    barycentricTriangleSubsimplex_face_zero 2 0,
    barycentricTriangleSubsimplex_face_zero 2 1]
  rw [barycentricTriangleSubsimplex_midpoint_pair 0,
    barycentricTriangleSubsimplex_midpoint_pair 1,
    barycentricTriangleSubsimplex_midpoint_pair 2,
    barycentricTriangleSubsimplex_radial_two,
    barycentricTriangleSubsimplex_radial_one,
    barycentricTriangleSubsimplex_radial_zero]
  rw [barycentricallySubdividedBoundary]
  repeat rw [Fin.sum_univ_three]
  simp only [barycentricEdgeSubdivision]
  repeat rw [Fin.sum_univ_two]
  norm_num
  module

/-- Linear extension of the six-cell subdivision to every singular two-chain. -/
def barycentricTriangleSubdivisionMorphism :
    SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 2 :=
  Limits.Sigma.desc fun simplex =>
    ModuleCat.ofHom
      { toFun := fun coefficient => coefficient • barycentricTriangleSubdivision simplex
        map_add' := fun left right => add_smul left right _
        map_smul' := by
          intro scalar coefficient
          simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
          rfl }

@[simp]
theorem barycentricTriangleSubdivisionMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 2) :
    barycentricTriangleSubdivisionMorphism (simplexGenerator simplex) =
      barycentricTriangleSubdivision simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => ModuleCat.ofHom
          { toFun := fun coefficient : ℚ =>
              coefficient • barycentricTriangleSubdivision source
            map_add' := fun left right => add_smul left right _
            map_smul' := by
              intro scalar coefficient
              simp only [RingHom.id_apply, smul_eq_mul, mul_smul] })) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

theorem barycentricallySubdividedBoundary_eq_morphism_boundary
    (simplex : SphereSingularSimplex 2) :
    barycentricallySubdividedBoundary simplex =
      barycentricEdgeSubdivisionMorphism
        (SphereSingularChainComplex.d 2 1 (simplexGenerator simplex)) := by
  rw [boundary_simplexGenerator, map_sum, barycentricallySubdividedBoundary]
  apply Finset.sum_congr rfl
  intro outerFace _
  rw [map_smul, barycentricEdgeSubdivisionMorphism_simplexGenerator]

/-- Exact recursive chain-map square in degrees `2 → 1`: the six-cell triangle boundary is the
two-half subdivision of the original boundary. -/
theorem barycentricTriangleSubdivisionMorphism_comp_boundary :
    barycentricTriangleSubdivisionMorphism ≫ SphereSingularChainComplex.d 2 1 =
      SphereSingularChainComplex.d 2 1 ≫ barycentricEdgeSubdivisionMorphism := by
  let left : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 1 :=
    barycentricTriangleSubdivisionMorphism ≫ SphereSingularChainComplex.d 2 1
  let right : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 1 :=
    SphereSingularChainComplex.d 2 1 ≫ barycentricEdgeSubdivisionMorphism
  have hleftRight : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change ℚ at coefficient
    simp only [left, right, ConcreteCategory.comp_apply]
    rw [Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
    change SphereSingularChainComplex.d 2 1
        (barycentricTriangleSubdivisionMorphism
          (coefficient • simplexGenerator simplex)) =
      barycentricEdgeSubdivisionMorphism
        (SphereSingularChainComplex.d 2 1
          (coefficient • simplexGenerator simplex))
    simp only [map_smul, barycentricTriangleSubdivisionMorphism_simplexGenerator,
      boundary_barycentricTriangleSubdivision,
      barycentricallySubdividedBoundary_eq_morphism_boundary]
  exact hleftRight

theorem boundary_barycentricTriangleSubdivisionMorphism (chain : SphereChain 2) :
    SphereSingularChainComplex.d 2 1
        (barycentricTriangleSubdivisionMorphism chain) =
      barycentricEdgeSubdivisionMorphism
        (SphereSingularChainComplex.d 2 1 chain) := by
  simpa only [ConcreteCategory.comp_apply] using
    congrArg (fun morphism : SphereSingularChainComplex.X 2 ⟶
      SphereSingularChainComplex.X 1 => morphism chain)
      barycentricTriangleSubdivisionMorphism_comp_boundary

/-- Exact squared coordinate distance on the source simplex.  This is a receiver of the ambient
Euclidean metric with no square-root or floating representation. -/
def triangleSquaredCoordinateDistance (left right : Triangle) : ℝ :=
  ∑ coordinate : Fin 3, (left coordinate - right coordinate) ^ 2

theorem triangleSquaredCoordinateDistance_nonneg (left right : Triangle) :
    0 ≤ triangleSquaredCoordinateDistance left right := by
  exact Finset.sum_nonneg fun coordinate _ => sq_nonneg _

theorem barycentricQuadratic_contraction (a b c : ℝ) (hsum : a + b + c = 0) :
    (a / 3) ^ 2 + (a / 3 + b / 2) ^ 2 +
        (a / 3 + b / 2 + c) ^ 2 ≤
      ((4 : ℝ) / 9) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hc : c = -a - b := by linarith
  rw [hc]
  nlinarith [sq_nonneg (4 * a - b), sq_nonneg b]

/-- Every one of the six barycentric maps contracts exact squared coordinate distance by the
uniform rational factor `4/9`. -/
theorem triangleSquaredCoordinateDistance_barycentricTriangleMap
    (outerFace : Fin 3) (half : Fin 2) (left right : Triangle) :
    triangleSquaredCoordinateDistance
        (barycentricTriangleMap outerFace half left)
        (barycentricTriangleMap outerFace half right) ≤
      ((4 : ℝ) / 9) * triangleSquaredCoordinateDistance left right := by
  have hleft := stdSimplex.sum_eq_one left
  have hright := stdSimplex.sum_eq_one right
  rw [Fin.sum_univ_three] at hleft hright
  fin_cases outerFace <;> fin_cases half <;>
    simp only [triangleSquaredCoordinateDistance, barycentricTriangleMap,
      triangleAffineMap_apply, Fin.sum_univ_three] <;>
    simp [barycentricTriangleVertices_zero, barycentricTriangleVertices_one,
      barycentricTriangleVertices_two, Fin.succAbove]
  all_goals
    have hsum :
        (left 0 - right 0) + (left 1 - right 1) + (left 2 - right 2) = 0 := by
      linarith
    have hcontract := barycentricQuadratic_contraction
      (left 0 - right 0) (left 1 - right 1) (left 2 - right 2) hsum
    norm_num at hcontract ⊢
    nlinarith [hcontract]

abbrev BarycentricTriangleAddress := Fin 3 × Fin 2

/-- The complete source map of one addressed descendant word. -/
def barycentricTriangleWordMap : List BarycentricTriangleAddress → C(Triangle, Triangle)
  | [] => ContinuousMap.id Triangle
  | address :: tail =>
      (barycentricTriangleWordMap tail).comp
        (barycentricTriangleMap address.1 address.2)

/-- Concatenating addressed refinements is literal serial composition.  Consequently every
longer word factors through the image of each of its prefixes; this is the lineage law used when
several source simplices are synchronized at one common scale. -/
theorem barycentricTriangleWordMap_append
    (first second : List BarycentricTriangleAddress) :
    barycentricTriangleWordMap (first ++ second) =
      (barycentricTriangleWordMap second).comp
        (barycentricTriangleWordMap first) := by
  induction first with
  | nil =>
      apply ContinuousMap.ext
      intro point
      rfl
  | cons address tail inductionHypothesis =>
      simp only [List.cons_append, barycentricTriangleWordMap,
        inductionHypothesis, ContinuousMap.comp_assoc]

/-- Every descendant word contracts by the exact power `(4/9)^word.length`; this is the uniform
geometric law absent from the three-cone operator. -/
theorem triangleSquaredCoordinateDistance_barycentricTriangleWordMap
    (word : List BarycentricTriangleAddress) (left right : Triangle) :
    triangleSquaredCoordinateDistance
        (barycentricTriangleWordMap word left)
        (barycentricTriangleWordMap word right) ≤
      ((4 : ℝ) / 9) ^ word.length *
        triangleSquaredCoordinateDistance left right := by
  induction word generalizing left right with
  | nil =>
      simp [barycentricTriangleWordMap]
  | cons address tail inductionHypothesis =>
      rw [barycentricTriangleWordMap, ContinuousMap.comp_apply]
      calc
        triangleSquaredCoordinateDistance
            (barycentricTriangleWordMap tail
              (barycentricTriangleMap address.1 address.2 left))
            (barycentricTriangleWordMap tail
              (barycentricTriangleMap address.1 address.2 right)) ≤
            ((4 : ℝ) / 9) ^ tail.length *
              triangleSquaredCoordinateDistance
                (barycentricTriangleMap address.1 address.2 left)
                (barycentricTriangleMap address.1 address.2 right) :=
          inductionHypothesis _ _
        _ ≤ ((4 : ℝ) / 9) ^ tail.length *
              (((4 : ℝ) / 9) * triangleSquaredCoordinateDistance left right) := by
          exact mul_le_mul_of_nonneg_left
            (triangleSquaredCoordinateDistance_barycentricTriangleMap
              address.1 address.2 left right) (by positivity)
        _ = ((4 : ℝ) / 9) ^ (address :: tail).length *
              triangleSquaredCoordinateDistance left right := by
          simp only [List.length_cons, pow_succ]
          ring

section Audit

#print axioms barycentricTriangleMap_face_zero
#print axioms boundary_barycentricTriangleSubdivision
#print axioms barycentricTriangleSubdivisionMorphism_comp_boundary
#print axioms triangleSquaredCoordinateDistance_barycentricTriangleMap
#print axioms barycentricTriangleWordMap_append
#print axioms triangleSquaredCoordinateDistance_barycentricTriangleWordMap

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
