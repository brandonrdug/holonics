import ElementaryHolonics.Millennium.HodgeStellarSubdivisionMeshObstruction

/-!
# The edge-refining first stage of barycentric subdivision

The three-cone triangle operator fails cover-smallness because it never refines an exterior edge.
The recursive barycentric construction begins one degree lower: split every addressed singular
edge at the exact midpoint, retain both oriented half-edges, and prove their shared midpoint
cancels.  This file also proves that each half-edge contracts the source parameter distance by the
exact factor `1/2`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision

abbrev Segment := stdSimplex ℝ (Fin 2)

/-- The exact equal-weight centre of the standard one-simplex. -/
def segmentMidpoint : Segment :=
  ⟨fun _ => (2 : ℝ)⁻¹, by
    constructor
    · intro coordinate
      positivity
    · rw [Fin.sum_univ_two]
      norm_num⟩

@[simp]
theorem segmentMidpoint_apply (coordinate : Fin 2) :
    segmentMidpoint coordinate = (2 : ℝ)⁻¹ := rfl

/-- Affine transport determined by two addressed segment vertices. -/
def segmentAffineMap (vertices : Fin 2 → Segment) : C(Segment, Segment) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 2,
      point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex)
          (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 2, ∑ vertex : Fin 2,
            point vertex * vertices vertex coordinate =
          ∑ vertex : Fin 2, ∑ coordinate : Fin 2,
            point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 2, point vertex * 1 := by
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
theorem segmentAffineMap_apply (vertices : Fin 2 → Segment) (point : Segment)
    (coordinate : Fin 2) :
    segmentAffineMap vertices point coordinate =
      ∑ vertex : Fin 2, point vertex * vertices vertex coordinate := rfl

@[simp]
theorem segmentAffineMap_vertex (vertices : Fin 2 → Segment) (vertex : Fin 2) :
    segmentAffineMap vertices (stdSimplex.vertex vertex) = vertices vertex := by
  apply stdSimplex.ext
  funext coordinate
  rw [segmentAffineMap_apply, Fin.sum_univ_two]
  fin_cases vertex <;> simp

/-- The ordered vertices `[midpoint, retained endpoint]` of one half-edge. -/
def edgeConeVertices (omitted : Fin 2) : Fin 2 → Segment :=
  Fin.cases segmentMidpoint fun _ : Fin 1 =>
    stdSimplex.vertex (omitted.succAbove 0)

@[simp] theorem edgeConeVertices_zero (omitted : Fin 2) :
    edgeConeVertices omitted 0 = segmentMidpoint := rfl

@[simp] theorem edgeConeVertices_one (omitted : Fin 2) :
    edgeConeVertices omitted 1 = stdSimplex.vertex (omitted.succAbove 0) := rfl

def edgeConeMap (omitted : Fin 2) : C(Segment, Segment) :=
  segmentAffineMap (edgeConeVertices omitted)

@[simp] theorem segmentFaceMap_zero_zero (point : stdSimplex ℝ (Fin 1)) :
    simplexFaceMap (degree := 0) 0 point 0 = 0 := by
  change FunOnFinite.linearMap ℝ ℝ (0 : Fin 2).succAbove point 0 = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove]

@[simp] theorem segmentFaceMap_zero_one (point : stdSimplex ℝ (Fin 1)) :
    simplexFaceMap (degree := 0) 0 point 1 = point 0 := by
  change FunOnFinite.linearMap ℝ ℝ (0 : Fin 2).succAbove point 1 = point 0
  rw [FunOnFinite.linearMap_apply_apply]
  norm_num [Fin.succAbove]
  decide

@[simp] theorem segmentFaceMap_one_zero (point : stdSimplex ℝ (Fin 1)) :
    simplexFaceMap (degree := 0) 1 point 0 = point 0 := by
  change FunOnFinite.linearMap ℝ ℝ (1 : Fin 2).succAbove point 0 = point 0
  rw [FunOnFinite.linearMap_apply_apply]
  norm_num [Fin.succAbove]
  decide

@[simp] theorem segmentFaceMap_one_one (point : stdSimplex ℝ (Fin 1)) :
    simplexFaceMap (degree := 0) 1 point 1 = 0 := by
  change FunOnFinite.linearMap ℝ ℝ (1 : Fin 2).succAbove point 1 = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove]

@[simp]
theorem edgeConeMap_vertex_zero (omitted : Fin 2) :
    edgeConeMap omitted (stdSimplex.vertex 0) = segmentMidpoint := by
  simp [edgeConeMap]

@[simp]
theorem edgeConeMap_vertex_one (omitted : Fin 2) :
    edgeConeMap omitted (stdSimplex.vertex 1) =
      stdSimplex.vertex (omitted.succAbove 0) := by
  simp [edgeConeMap]

/-- Deleting the midpoint returns the addressed endpoint of the original edge. -/
theorem edgeConeMap_face_zero (omitted : Fin 2) :
    (edgeConeMap omitted).comp (simplexFaceMap (degree := 0) 0) =
      simplexFaceMap (degree := 0) omitted := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 2,
      simplexFaceMap (degree := 0) 0 point vertex *
        edgeConeVertices omitted vertex coordinate) =
    simplexFaceMap (degree := 0) omitted point coordinate
  fin_cases omitted <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_two, Fin.succAbove]

/-- The two half-edges share the same midpoint face. -/
theorem edgeConeMap_midpoint_pair :
    (edgeConeMap 0).comp (simplexFaceMap (degree := 0) 1) =
      (edgeConeMap 1).comp (simplexFaceMap (degree := 0) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 2,
      simplexFaceMap (degree := 0) 1 point vertex *
        edgeConeVertices 0 vertex coordinate) =
    ∑ vertex : Fin 2,
      simplexFaceMap (degree := 0) 1 point vertex *
        edgeConeVertices 1 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_two, Fin.succAbove]

/-- One geometric half of a singular edge. -/
def barycentricEdgeSubsimplex (omitted : Fin 2)
    (simplex : SphereSingularSimplex 1) : SphereSingularSimplex 1 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 1)) simplex).comp (edgeConeMap omitted))

theorem barycentricEdgeSubsimplex_face_zero (omitted : Fin 2)
    (simplex : SphereSingularSimplex 1) :
    simplexFace 0 (barycentricEdgeSubsimplex omitted simplex) =
      simplexFace omitted simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 0))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [barycentricEdgeSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, edgeConeMap_face_zero]

theorem barycentricEdgeSubsimplex_midpoint_pair (simplex : SphereSingularSimplex 1) :
    simplexFace 1 (barycentricEdgeSubsimplex 0 simplex) =
      simplexFace 1 (barycentricEdgeSubsimplex 1 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 0))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [barycentricEdgeSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, edgeConeMap_midpoint_pair]

/-- The oriented two-half subdivision of one singular edge. -/
def barycentricEdgeSubdivision (simplex : SphereSingularSimplex 1) : SphereChain 1 :=
  ∑ omitted : Fin 2, (-1 : ℚ) ^ (omitted : ℕ) •
    simplexGenerator (barycentricEdgeSubsimplex omitted simplex)

/-- The midpoint currents cancel and the original endpoint difference survives exactly. -/
theorem boundary_barycentricEdgeSubdivision (simplex : SphereSingularSimplex 1) :
    SphereSingularChainComplex.d 1 0 (barycentricEdgeSubdivision simplex) =
      SphereSingularChainComplex.d 1 0 (simplexGenerator simplex) := by
  rw [barycentricEdgeSubdivision, map_sum]
  simp only [map_smul, boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_two]
  rw [barycentricEdgeSubsimplex_face_zero 0,
    barycentricEdgeSubsimplex_face_zero 1,
    barycentricEdgeSubsimplex_midpoint_pair]
  norm_num
  module

/-- Linear extension of midpoint subdivision to every rational singular one-chain. -/
def barycentricEdgeSubdivisionMorphism :
    SphereSingularChainComplex.X 1 ⟶ SphereSingularChainComplex.X 1 :=
  Limits.Sigma.desc fun simplex =>
    ModuleCat.ofHom
      { toFun := fun coefficient => coefficient • barycentricEdgeSubdivision simplex
        map_add' := fun left right => add_smul left right _
        map_smul' := by
          intro scalar coefficient
          simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
          rfl }

@[simp]
theorem barycentricEdgeSubdivisionMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 1) :
    barycentricEdgeSubdivisionMorphism (simplexGenerator simplex) =
      barycentricEdgeSubdivision simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 1 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => ModuleCat.ofHom
          { toFun := fun coefficient : ℚ =>
              coefficient • barycentricEdgeSubdivision source
            map_add' := fun left right => add_smul left right _
            map_smul' := by
              intro scalar coefficient
              simp only [RingHom.id_apply, smul_eq_mul, mul_smul] })) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- Degree-one barycentric subdivision commutes with the endpoint boundary. -/
theorem barycentricEdgeSubdivisionMorphism_comp_boundary :
    barycentricEdgeSubdivisionMorphism ≫ SphereSingularChainComplex.d 1 0 =
      SphereSingularChainComplex.d 1 0 := by
  let left : SphereSingularChainComplex.X 1 ⟶ SphereSingularChainComplex.X 0 :=
    barycentricEdgeSubdivisionMorphism ≫ SphereSingularChainComplex.d 1 0
  let right : SphereSingularChainComplex.X 1 ⟶ SphereSingularChainComplex.X 0 :=
    SphereSingularChainComplex.d 1 0
  have hleftRight : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change ℚ at coefficient
    simp only [left, right, ConcreteCategory.comp_apply]
    rw [Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
    change SphereSingularChainComplex.d 1 0
        (barycentricEdgeSubdivisionMorphism
          (coefficient • simplexGenerator simplex)) =
      SphereSingularChainComplex.d 1 0 (coefficient • simplexGenerator simplex)
    rw [map_smul, barycentricEdgeSubdivisionMorphism_simplexGenerator]
    simpa only [map_smul] using
      congrArg (fun edgeChain => coefficient • edgeChain)
        (boundary_barycentricEdgeSubdivision simplex)
  exact hleftRight

/-- Source parameter distance on the segment; this retains orientation only through the ordered
coordinate difference and returns its unsigned receiver magnitude. -/
def segmentParameterDistance (left right : Segment) : ℝ :=
  |left 0 - right 0|

/-- Each addressed half-edge contracts parameter distance by exactly `1/2`. -/
theorem segmentParameterDistance_edgeConeMap (omitted : Fin 2)
    (left right : Segment) :
    segmentParameterDistance (edgeConeMap omitted left) (edgeConeMap omitted right) =
      (2 : ℝ)⁻¹ * segmentParameterDistance left right := by
  have hleft := stdSimplex.sum_eq_one left
  have hright := stdSimplex.sum_eq_one right
  rw [Fin.sum_univ_two] at hleft hright
  fin_cases omitted
  · simp only [segmentParameterDistance, edgeConeMap, segmentAffineMap_apply,
      Fin.sum_univ_two]
    change |(left 0 * (2 : ℝ)⁻¹ + left 1 * 0) -
        (right 0 * (2 : ℝ)⁻¹ + right 1 * 0)| =
      (2 : ℝ)⁻¹ * |left 0 - right 0|
    have hdifference :
        (left 0 * (2 : ℝ)⁻¹ + left 1 * 0) -
            (right 0 * (2 : ℝ)⁻¹ + right 1 * 0) =
          (2 : ℝ)⁻¹ * (left 0 - right 0) := by ring
    rw [hdifference, abs_mul]
    norm_num
  · simp only [segmentParameterDistance, edgeConeMap, segmentAffineMap_apply,
      Fin.sum_univ_two]
    change |(left 0 * (2 : ℝ)⁻¹ + left 1 * 1) -
        (right 0 * (2 : ℝ)⁻¹ + right 1 * 1)| =
      (2 : ℝ)⁻¹ * |left 0 - right 0|
    have hdifference :
        (left 0 * (2 : ℝ)⁻¹ + left 1) -
            (right 0 * (2 : ℝ)⁻¹ + right 1) =
          -(2 : ℝ)⁻¹ * (left 0 - right 0) := by
      linarith
    simp only [mul_one]
    rw [hdifference, abs_mul, abs_neg]
    norm_num

section Audit

#print axioms edgeConeMap_face_zero
#print axioms boundary_barycentricEdgeSubdivision
#print axioms segmentParameterDistance_edgeConeMap

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
