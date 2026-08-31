import ElementaryHolonics.Millennium.HodgePointCarry
import ElementaryHolonics.Millennium.HodgeRefinementWords
import ElementaryHolonics.Millennium.HodgeTetrahedralRealizationChainMap

/-!
# Exact radial current after arbitrary barycentric refinement

The point-natural star label is shared across every refined seam.  A point on an original
tetrahedral edge lies on the two radial faces opposite the complementary vertices, so its label is
one of the edge endpoints.  The original endpoints themselves have forced labels.  Consequently
every refined edge current is supported on one finite edge and has its exact terminal-minus-initial
boundary; edge rigidity returns the addressed edge atom.  The same support-plus-boundary argument
then returns every refined radial face atom.

Truth status: introduced maps are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to point-natural carrying, fixed-depth word expansion,
and the exact radial and finite-chain incidence laws.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRadialCurrent

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeTetrahedralRealizationChainMap
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeRadialSpernerCarry
open Soma.Holonics.Millennium.HodgePointCarry
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron

set_option maxHeartbeats 2000000

/-- [definition] First radial face containing each addressed tetrahedral edge. -/
def edgeMissingFirst : TetraEdge → Fin 4
  | .e01 => 2
  | .e02 => 1
  | .e03 => 1
  | .e12 => 0
  | .e13 => 0
  | .e23 => 0

/-- [definition] Second radial face containing each addressed tetrahedral edge. -/
def edgeMissingSecond : TetraEdge → Fin 4
  | .e01 => 3
  | .e02 => 3
  | .e03 => 2
  | .e12 => 3
  | .e13 => 2
  | .e23 => 1

/-- [definition] Local face index realizing the edge inside its first radial face. -/
def edgeFirstLocal : TetraEdge → Fin 3
  | .e01 => 2
  | .e02 => 2
  | .e03 => 1
  | .e12 => 2
  | .e13 => 1
  | .e23 => 0

/-- [definition] Ordered endpoint selected by a standard edge vertex. -/
def edgeEndpoint (edge : TetraEdge) : Fin 2 → Fin 4 :=
  Fin.cases (edgeInitial edge) (fun _ => edgeTerminal edge)

/-- [proved-derived; formal-checked] Every point of an addressed radial edge is a point of its
first complementary radial face. -/
theorem edgeSimplex_point_on_first (edge : TetraEdge) (point : Segment) :
    ∃ source : Triangle,
      TopCat.toSSetObjEquiv sphereTopCat
          (Opposite.op (SimplexCategory.mk 1)) (edgeSimplex edge) point =
        radialFace (edgeMissingFirst edge) source := by
  cases edge with
  | e01 =>
      refine ⟨simplexFaceMap (degree := 1) 2 point, ?_⟩
      rw [edgeSimplex, simplexFace_realization]
      rfl
  | e02 =>
      refine ⟨simplexFaceMap (degree := 1) 2 point, ?_⟩
      rw [edgeSimplex, simplexFace_realization]
      rfl
  | e03 =>
      refine ⟨simplexFaceMap (degree := 1) 1 point, ?_⟩
      rw [edgeSimplex, simplexFace_realization]
      rfl
  | e12 =>
      refine ⟨simplexFaceMap (degree := 1) 2 point, ?_⟩
      rw [edgeSimplex, simplexFace_realization]
      rfl
  | e13 =>
      refine ⟨simplexFaceMap (degree := 1) 1 point, ?_⟩
      rw [edgeSimplex, simplexFace_realization]
      rfl
  | e23 =>
      refine ⟨simplexFaceMap (degree := 1) 0 point, ?_⟩
      rw [edgeSimplex, simplexFace_realization]
      rfl

/-- [proved-derived; formal-checked] The same edge point lies on its second complementary radial
face; the six equalities are exactly the retained radial seam laws. -/
theorem edgeSimplex_point_on_second (edge : TetraEdge) (point : Segment) :
    ∃ source : Triangle,
      TopCat.toSSetObjEquiv sphereTopCat
          (Opposite.op (SimplexCategory.mk 1)) (edgeSimplex edge) point =
        radialFace (edgeMissingSecond edge) source := by
  cases edge with
  | e01 =>
      refine ⟨simplexFaceMap (degree := 1) 2 point, ?_⟩
      rw [edgeSimplex, radialSingularSimplex_edge_01, simplexFace_realization]
      rfl
  | e02 =>
      refine ⟨simplexFaceMap (degree := 1) 1 point, ?_⟩
      rw [edgeSimplex, radialSingularSimplex_edge_02, simplexFace_realization]
      rfl
  | e03 =>
      refine ⟨simplexFaceMap (degree := 1) 1 point, ?_⟩
      rw [edgeSimplex, radialSingularSimplex_edge_03, simplexFace_realization]
      rfl
  | e12 =>
      refine ⟨simplexFaceMap (degree := 1) 0 point, ?_⟩
      rw [edgeSimplex, radialSingularSimplex_edge_12, simplexFace_realization]
      rfl
  | e13 =>
      refine ⟨simplexFaceMap (degree := 1) 0 point, ?_⟩
      rw [edgeSimplex, radialSingularSimplex_edge_13, simplexFace_realization]
      rfl
  | e23 =>
      refine ⟨simplexFaceMap (degree := 1) 0 point, ?_⟩
      rw [edgeSimplex, radialSingularSimplex_edge_23, simplexFace_realization]
      rfl

/-- [proved-derived; formal-checked] Every standard vertex of an addressed edge is exactly a
radial tetrahedron vertex in its first containing face. -/
theorem edgeSimplex_vertex_radial (edge : TetraEdge) (index : Fin 2) :
    simplexVertexPoint (edgeSimplex edge) index =
      radialFace (edgeMissingFirst edge)
        (stdSimplex.vertex ((edgeFirstLocal edge).succAbove index)) := by
  rw [simplexVertexPoint]
  cases edge <;>
    rw [edgeSimplex, simplexFace_realization, ContinuousMap.comp_apply] <;>
    simp only [radialSingularSimplex, Equiv.apply_symm_apply] <;>
    simp only [edgeMissingFirst, edgeFirstLocal]
  all_goals
    apply congrArg (radialFace _)
    exact Soma.Holonics.Millennium.HodgePointCarry.simplexFaceMap_vertex _ _

/-- [proved-derived; formal-checked] The composite radial-face vertex address is the original
ordered tetrahedral edge endpoint. -/
theorem radialEdge_vertex_address (edge : TetraEdge) (index : Fin 2) :
    (edgeMissingFirst edge).succAbove ((edgeFirstLocal edge).succAbove index) =
      edgeEndpoint edge index := by
  cases edge <;> fin_cases index <;>
    rfl

/-- [proved-derived; formal-checked] Point-star carrying forces the exact original label at each
endpoint of every addressed radial edge. -/
theorem edgeSimplex_endpoint_label (lebesgue : StarLebesgueLabel)
    (edge : TetraEdge) (index : Fin 2) :
    simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) (edgeSimplex edge) index = edgeEndpoint edge index := by
  have carried := simplexVertexPoint_mem_labelStar lebesgue (edgeSimplex edge) index
  rw [edgeSimplex_vertex_radial edge index] at carried
  calc
    simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) (edgeSimplex edge) index =
      (edgeMissingFirst edge).succAbove ((edgeFirstLocal edge).succAbove index) := by
        exact radialVertex_carried_label_eq
          (edgeMissingFirst edge) ((edgeFirstLocal edge).succAbove index) _ carried
    _ = edgeEndpoint edge index := radialEdge_vertex_address edge index

/-- [proved-derived; formal-checked] Avoiding the two complementary face labels leaves exactly
the two endpoint labels of the addressed edge. -/
theorem label_eq_edgeEndpoint_of_ne_missing (edge : TetraEdge) (label : Fin 4)
    (first : label ≠ edgeMissingFirst edge)
    (second : label ≠ edgeMissingSecond edge) :
    label = edgeInitial edge ∨ label = edgeTerminal edge := by
  cases edge <;> fin_cases label <;>
    simp_all [edgeMissingFirst, edgeMissingSecond, edgeInitial, edgeTerminal, Fin.ext_iff]

/-- [proved-derived; formal-checked] The label at every vertex of every addressed refined edge
word remains one of the two original edge endpoints. -/
theorem edgeWord_vertex_label_allowed (lebesgue : StarLebesgueLabel) (edge : TetraEdge)
    {scale : ℕ} (word : EdgeWord scale) (index : Fin 2) :
    simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue)
        (edgeWordSubsimplex word (edgeSimplex edge)) index = edgeInitial edge ∨
      simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue)
        (edgeWordSubsimplex word (edgeSimplex edge)) index = edgeTerminal edge := by
  let source : Segment := edgeWordMap (edgeWordList word) (stdSimplex.vertex index)
  have realized :
      simplexVertexPoint (edgeWordSubsimplex word (edgeSimplex edge)) index =
        TopCat.toSSetObjEquiv sphereTopCat
          (Opposite.op (SimplexCategory.mk 1)) (edgeSimplex edge) source := by
    rfl
  obtain ⟨firstSource, firstLaw⟩ := edgeSimplex_point_on_first edge source
  obtain ⟨secondSource, secondLaw⟩ := edgeSimplex_point_on_second edge source
  apply label_eq_edgeEndpoint_of_ne_missing edge
  · apply radial_carried_label_ne_opposite (edgeMissingFirst edge) _ firstSource
    rw [← firstLaw, ← realized]
    exact simplexVertexPoint_mem_labelStar lebesgue
      (edgeWordSubsimplex word (edgeSimplex edge)) index
  · apply radial_carried_label_ne_opposite (edgeMissingSecond edge) _ secondSource
    rw [← secondLaw, ← realized]
    exact simplexVertexPoint_mem_labelStar lebesgue
      (edgeWordSubsimplex word (edgeSimplex edge)) index

/-- [proved-derived; formal-checked] Every refined edge atom carries current only on its original
addressed edge. -/
theorem pointCarry_edgeWord_supported (lebesgue : StarLebesgueLabel) (edge observed : TetraEdge)
    {scale : ℕ} (word : EdgeWord scale) (different : observed ≠ edge) :
    pointCarry
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 1
        (edgeWordSubsimplex word (edgeSimplex edge)) observed = 0 := by
  exact orientedEdgeCarry_supported_on_edge edge
    (simplexPointLabels
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) (edgeWordSubsimplex word (edgeSimplex edge)) 0)
    (simplexPointLabels
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) (edgeWordSubsimplex word (edgeSimplex edge)) 1)
    (edgeWord_vertex_label_allowed lebesgue edge word 0)
    (edgeWord_vertex_label_allowed lebesgue edge word 1)
    observed different

/-- [proved-derived; formal-checked] Carrying a zero-face of an addressed edge returns the finite
vertex selected by that same zero-face. -/
theorem pointCarry_edgeFace (lebesgue : StarLebesgueLabel) (edge : TetraEdge)
    (face : Fin 2) :
    pointCarry
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 0 (simplexFace face (edgeSimplex edge)) =
      vertexUnit (edgeEndpoint edge (face.succAbove 0)) := by
  rw [pointCarry, labelledSimplexCarry_zero]
  congr 1
  have faceLaw := congrFun
    (simplexPointLabels_face
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) (edgeSimplex edge) face) 0
  rw [faceLaw]
  exact edgeSimplex_endpoint_label lebesgue edge (face.succAbove 0)

/-- [proved-derived; formal-checked] The point current of one original radial edge boundary is
the canonical terminal-minus-initial finite vertex current. -/
theorem pointCarry_edgeSimplex_boundary (lebesgue : StarLebesgueLabel)
    (edge : TetraEdge) :
    pointCarryMorphism
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 0
        (SphereSingularChainComplex.d 1 0
          (simplexGenerator (edgeSimplex edge))) =
      vertexUnit (edgeTerminal edge) - vertexUnit (edgeInitial edge) := by
  rw [boundary_simplexGenerator, Fin.sum_univ_two]
  norm_num
  rw [pointCarry_edgeFace lebesgue edge 0,
    pointCarry_edgeFace lebesgue edge 1]
  cases edge <;>
    simp [edgeEndpoint, Fin.succAbove, edgeInitial, edgeTerminal, sub_eq_add_neg]
  all_goals
    congr 1

/-- [proved-derived; formal-checked] The complete carried current of an iterated edge refinement
is supported on the original addressed edge. -/
theorem refinedEdgeCurrent_supported (lebesgue : StarLebesgueLabel)
    (scale : ℕ) (edge observed : TetraEdge) (different : observed ≠ edge) :
    pointCarryMorphism
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 1
        (iteratedBarycentricEdgeSubdivision scale
          (simplexGenerator (edgeSimplex edge))) observed = 0 := by
  rw [edgeWordExpansion, map_sum]
  simp only [map_smul, pointCarryMorphism_simplexGenerator]
  rw [Fintype.sum_apply observed]
  apply Finset.sum_eq_zero
  intro word _
  have hpoint := pointCarryMorphism_simplexGenerator
    (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling lebesgue)
    1 (edgeWordSubsimplex word (edgeSimplex edge))
  have hpointScaled := congrArg (fun z : EdgeChain => edgeWordSign word • z) hpoint
  have hpointObs := congrArg (fun z : EdgeChain => z observed) hpointScaled
  rw [hpointObs]
  change edgeWordSign word *
      pointCarry
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 1
        (edgeWordSubsimplex word (edgeSimplex edge)) observed = 0
  rw [pointCarry_edgeWord_supported lebesgue edge observed word different, mul_zero]

/-- [proved-derived; formal-checked] Every iterated radial edge refinement returns the original
canonical terminal-minus-initial boundary. -/
theorem refinedEdgeCurrent_boundary (lebesgue : StarLebesgueLabel)
    (scale : ℕ) (edge : TetraEdge) :
    vertexBoundary
        (pointCarryMorphism
          (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
            lebesgue) 1
          (iteratedBarycentricEdgeSubdivision scale
            (simplexGenerator (edgeSimplex edge)))) =
      vertexUnit (edgeTerminal edge) - vertexUnit (edgeInitial edge) := by
  rw [← pointCarryMorphism_boundary_one]
  rw [boundary_iteratedBarycentricEdgeSubdivision]
  exact pointCarry_edgeSimplex_boundary lebesgue edge

/-- [proved-derived; formal-checked] **REFINED RADIAL EDGE RIGIDITY.**  At every depth, the point
current of the barycentrically refined radial edge is exactly its addressed finite edge atom. -/
theorem refinedEdgeCurrent (lebesgue : StarLebesgueLabel)
    (scale : ℕ) (edge : TetraEdge) :
    pointCarryMorphism
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 1
        (iteratedBarycentricEdgeSubdivision scale
          (simplexGenerator (edgeSimplex edge))) = edgeUnit edge := by
  apply edgeChain_eq_edgeUnit_of_supported_boundary edge
  · intro observed different
    exact refinedEdgeCurrent_supported lebesgue scale edge observed different
  · exact refinedEdgeCurrent_boundary lebesgue scale edge

/-- [proved-derived; formal-checked] Iterated edge refinement is additive.  The theorem records
linearity at the actual fixed-depth transport owner rather than treating the word census as a
separate algorithm. -/
theorem iteratedBarycentricEdgeSubdivision_add (scale : ℕ)
    (left right : SphereChain 1) :
    iteratedBarycentricEdgeSubdivision scale (left + right) =
      iteratedBarycentricEdgeSubdivision scale left +
        iteratedBarycentricEdgeSubdivision scale right := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricEdgeSubdivisionMorphism
          (iteratedBarycentricEdgeSubdivision scale (left + right)) =
        barycentricEdgeSubdivisionMorphism
            (iteratedBarycentricEdgeSubdivision scale left) +
          barycentricEdgeSubdivisionMorphism
            (iteratedBarycentricEdgeSubdivision scale right)
      rw [inductionHypothesis, map_add]

/-- [proved-derived; formal-checked] Iterated edge refinement preserves addressed rational
coefficients exactly. -/
theorem iteratedBarycentricEdgeSubdivision_smul (scale : ℕ) (coefficient : ℚ)
    (chain : SphereChain 1) :
    iteratedBarycentricEdgeSubdivision scale (coefficient • chain) =
      coefficient • iteratedBarycentricEdgeSubdivision scale chain := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricEdgeSubdivisionMorphism
          (iteratedBarycentricEdgeSubdivision scale (coefficient • chain)) =
        coefficient • barycentricEdgeSubdivisionMorphism
          (iteratedBarycentricEdgeSubdivision scale chain)
      rw [inductionHypothesis, map_smul]

/-- [proved-derived; formal-checked] The point-natural current is a left inverse to
the complete six-edge realization after every common barycentric refinement depth.  This is the
finite seam-gluing law needed by the radial faces; it applies to arbitrary edge coefficients, not
only to a single named occurrence. -/
theorem refinedEdgeRealizationCurrent (lebesgue : StarLebesgueLabel)
    (scale : ℕ) (chain : EdgeChain) :
    pointCarryMorphism
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 1
        (iteratedBarycentricEdgeSubdivision scale (edgeRealization chain)) = chain := by
  change pointCarryMorphism
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) 1
      (iteratedBarycentricEdgeSubdivision scale
        (chain .e01 • simplexGenerator (edgeSimplex .e01) +
         chain .e02 • simplexGenerator (edgeSimplex .e02) +
         chain .e03 • simplexGenerator (edgeSimplex .e03) +
         chain .e12 • simplexGenerator (edgeSimplex .e12) +
         chain .e13 • simplexGenerator (edgeSimplex .e13) +
         chain .e23 • simplexGenerator (edgeSimplex .e23))) = chain
  simp only [iteratedBarycentricEdgeSubdivision_add,
    iteratedBarycentricEdgeSubdivision_smul, map_add, map_smul]
  have hE01 := congrArg (fun z : EdgeChain => chain .e01 • z)
    (refinedEdgeCurrent lebesgue scale .e01)
  have hE02 := congrArg (fun z : EdgeChain => chain .e02 • z)
    (refinedEdgeCurrent lebesgue scale .e02)
  have hE03 := congrArg (fun z : EdgeChain => chain .e03 • z)
    (refinedEdgeCurrent lebesgue scale .e03)
  have hE12 := congrArg (fun z : EdgeChain => chain .e12 • z)
    (refinedEdgeCurrent lebesgue scale .e12)
  have hE13 := congrArg (fun z : EdgeChain => chain .e13 • z)
    (refinedEdgeCurrent lebesgue scale .e13)
  have hE23 := congrArg (fun z : EdgeChain => chain .e23 • z)
    (refinedEdgeCurrent lebesgue scale .e23)
  rw [hE01, hE02, hE03, hE12, hE13, hE23]
  funext observed
  change
    chain .e01 * (if observed = .e01 then 1 else 0) +
      chain .e02 * (if observed = .e02 then 1 else 0) +
      chain .e03 * (if observed = .e03 then 1 else 0) +
      chain .e12 * (if observed = .e12 then 1 else 0) +
      chain .e13 * (if observed = .e13 then 1 else 0) +
      chain .e23 * (if observed = .e23 then 1 else 0) = chain observed
  cases observed <;> simp

/-- [proved-derived; formal-checked] A finite addressed face realizes as precisely its radial
singular simplex, with no additional occurrence. -/
theorem faceRealization_faceUnit (face : Fin 4) :
    faceRealization (faceUnit face) =
      simplexGenerator (radialSingularSimplex face) := by
  fin_cases face <;>
    simp [faceRealization, faceUnit, Fin.sum_univ_four]

/-- [proved-derived; formal-checked] Every vertex of every fixed-depth descendant of a radial
face remains geometrically on that same radial face. -/
theorem triangleWord_vertex_on_radialFace (face : Fin 4) {scale : ℕ}
    (word : TriangleWord scale) (index : Fin 3) :
    ∃ source : Triangle,
      simplexVertexPoint
          (triangleWordSubsimplex word (radialSingularSimplex face)) index =
        radialFace face source := by
  refine ⟨barycentricTriangleWordMap (triangleWordList word)
    (stdSimplex.vertex index), ?_⟩
  rfl

/-- [proved-derived; formal-checked] Every refined radial-face atom is supported only on its
original addressed finite face. -/
theorem pointCarry_triangleWord_supported (lebesgue : StarLebesgueLabel)
    (face observed : Fin 4) {scale : ℕ} (word : TriangleWord scale)
    (different : observed ≠ face) :
    pointCarry
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 2
        (triangleWordSubsimplex word (radialSingularSimplex face)) observed = 0 := by
  exact pointCarry_supported_on_radialFace lebesgue face
    (triangleWordSubsimplex word (radialSingularSimplex face))
    (triangleWord_vertex_on_radialFace face word) observed different

/-- [proved-derived; formal-checked] The complete carried current of a refined radial face has no
coordinate outside its original addressed face. -/
theorem refinedFaceCurrent_supported (lebesgue : StarLebesgueLabel)
    (scale : ℕ) (face observed : Fin 4) (different : observed ≠ face) :
    pointCarryMorphism
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 2
        (iteratedBarycentricTriangleSubdivision scale
          (simplexGenerator (radialSingularSimplex face))) observed = 0 := by
  rw [triangleWordExpansion, map_sum]
  simp only [map_smul, pointCarryMorphism_simplexGenerator]
  rw [Fintype.sum_apply observed]
  apply Finset.sum_eq_zero
  intro word _
  have hpoint := pointCarryMorphism_simplexGenerator
    (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling lebesgue)
    2 (triangleWordSubsimplex word (radialSingularSimplex face))
  have hpointScaled := congrArg (fun z : FaceChain => triangleWordSign word • z) hpoint
  have hpointObs := congrArg (fun z : FaceChain => z observed) hpointScaled
  rw [hpointObs]
  change triangleWordSign word *
      pointCarry
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 2
        (triangleWordSubsimplex word (radialSingularSimplex face)) observed = 0
  rw [pointCarry_triangleWord_supported lebesgue face observed word different, mul_zero]

/-- [proved-derived; formal-checked] Every refined radial face returns the exact three-edge
boundary of its addressed finite face. -/
theorem refinedFaceCurrent_boundary (lebesgue : StarLebesgueLabel)
    (scale : ℕ) (face : Fin 4) :
    faceBoundary
        (pointCarryMorphism
          (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
            lebesgue) 2
          (iteratedBarycentricTriangleSubdivision scale
            (simplexGenerator (radialSingularSimplex face)))) =
      faceBoundary (faceUnit face) := by
  rw [← pointCarryMorphism_boundary_two]
  rw [boundary_iteratedBarycentricTriangleSubdivision]
  rw [← faceRealization_faceUnit face, faceRealization_boundary]
  exact refinedEdgeRealizationCurrent lebesgue scale (faceBoundary (faceUnit face))

/-- [proved-derived; formal-checked] **REFINED RADIAL FACE RIGIDITY.**  At every
depth, the point-natural current of a barycentrically refined radial face is exactly its addressed
finite face atom. -/
theorem refinedFaceCurrent (lebesgue : StarLebesgueLabel)
    (scale : ℕ) (face : Fin 4) :
    pointCarryMorphism
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 2
        (iteratedBarycentricTriangleSubdivision scale
          (simplexGenerator (radialSingularSimplex face))) = faceUnit face := by
  apply faceChain_eq_faceUnit_of_supported_boundary face
  · intro observed different
    exact refinedFaceCurrent_supported lebesgue scale face observed different
  · exact refinedFaceCurrent_boundary lebesgue scale face

/-- [proved-derived; formal-checked] Iterated triangle refinement is additive. -/
theorem iteratedBarycentricTriangleSubdivision_add (scale : ℕ)
    (left right : SphereChain 2) :
    iteratedBarycentricTriangleSubdivision scale (left + right) =
      iteratedBarycentricTriangleSubdivision scale left +
        iteratedBarycentricTriangleSubdivision scale right := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricTriangleSubdivisionMorphism
          (iteratedBarycentricTriangleSubdivision scale (left + right)) =
        barycentricTriangleSubdivisionMorphism
            (iteratedBarycentricTriangleSubdivision scale left) +
          barycentricTriangleSubdivisionMorphism
            (iteratedBarycentricTriangleSubdivision scale right)
      rw [inductionHypothesis, map_add]

/-- [proved-derived; formal-checked] Iterated triangle refinement preserves rational
coefficients. -/
theorem iteratedBarycentricTriangleSubdivision_smul (scale : ℕ) (coefficient : ℚ)
    (chain : SphereChain 2) :
    iteratedBarycentricTriangleSubdivision scale (coefficient • chain) =
      coefficient • iteratedBarycentricTriangleSubdivision scale chain := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricTriangleSubdivisionMorphism
          (iteratedBarycentricTriangleSubdivision scale (coefficient • chain)) =
        coefficient • barycentricTriangleSubdivisionMorphism
          (iteratedBarycentricTriangleSubdivision scale chain)
      rw [inductionHypothesis, map_smul]

/-- [proved-derived; formal-checked] Iterated triangle refinement distributes over every finite
addressed occurrence population. -/
theorem iteratedBarycentricTriangleSubdivision_sum {index : Type*}
    [Fintype index] (scale : ℕ) (chain : index → SphereChain 2) :
    iteratedBarycentricTriangleSubdivision scale (∑ i, chain i) =
      ∑ i, iteratedBarycentricTriangleSubdivision scale (chain i) := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricTriangleSubdivisionMorphism
          (iteratedBarycentricTriangleSubdivision scale (∑ i, chain i)) =
        ∑ i, barycentricTriangleSubdivisionMorphism
          (iteratedBarycentricTriangleSubdivision scale (chain i))
      rw [inductionHypothesis, map_sum]

/-- [proved-derived; formal-checked] The alternating four-face singular sphere
returns the nonzero finite fundamental current after every common refinement depth.  Thus the
point-natural receiver sees the same global class through all admitted local refinements. -/
theorem refinedSphereFundamentalCurrent (lebesgue : StarLebesgueLabel)
    (scale : ℕ) :
    pointCarryMorphism
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 2
        (iteratedBarycentricTriangleSubdivision scale sphereFundamentalCandidate) =
      fundamentalFaceChain := by
  rw [sphereFundamentalCandidate,
    iteratedBarycentricTriangleSubdivision_sum, map_sum]
  simp_rw [iteratedBarycentricTriangleSubdivision_smul, map_smul]
  have hF0 := refinedFaceCurrent lebesgue scale 0
  have hF1 := refinedFaceCurrent lebesgue scale 1
  have hF2 := refinedFaceCurrent lebesgue scale 2
  have hF3 := refinedFaceCurrent lebesgue scale 3
  funext observed
  rw [Fintype.sum_apply observed]
  rw [Fin.sum_univ_four]
  rw [hF0, hF1, hF2, hF3]
  have hneg : ∀ (f : FaceChain) (i : Fin 4), (-f) i = -f i := by
    intro f i
    rfl
  fin_cases observed <;>
    norm_num [fundamentalFaceChain, faceUnit, hneg, Fin.ext_iff]

section Audit

#print axioms edgeSimplex_point_on_first
#print axioms edgeSimplex_point_on_second
#print axioms edgeWord_vertex_label_allowed
#print axioms pointCarry_edgeWord_supported
#print axioms edgeSimplex_endpoint_label
#print axioms refinedEdgeCurrent
#print axioms refinedEdgeRealizationCurrent
#print axioms refinedFaceCurrent
#print axioms refinedSphereFundamentalCurrent

end Audit

end Soma.Holonics.Millennium.HodgeRadialCurrent
