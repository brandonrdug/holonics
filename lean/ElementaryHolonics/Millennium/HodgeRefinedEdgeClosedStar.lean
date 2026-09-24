import ElementaryHolonics.Millennium.HodgeBarycentricEdgeCoverSmallness
import ElementaryHolonics.Millennium.HodgeFiniteClosedStarLabeling
import ElementaryHolonics.Millennium.HodgePointCarry

/-!
# Globally addressed refined singular edges

This file supplies the degree-one carrier parallel to the refined triangle carrier.  A cell keeps
an actual supported singular edge and a finite barycentric edge word.  Its tetrahedral presentation
is deliberately degenerate: three tetrahedral vertices map to the first segment endpoint and the
fourth maps to the second.  An explicit section of this collapse proves that no part of the
original edge image is lost by the presentation.

Truth status: definitions are `[definition]`; construction theorems are
`[proved-derived; formal-checked]` relative to exact edge-word cover-smallness and the finite
closed-star labeling constructor.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRefinedEdgeClosedStar

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set Topology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricEdgeCoverSmallness
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeBarycentricChainSupport
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgePointCarry
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-! ## The degenerate tetrahedral edge presentation -/

/-- [definition] The affine collapse from a tetrahedron to its retained segment. -/
def tetrahedronToSegment : C(Tetrahedron, Segment) where
  toFun := stdSimplex.map ![0, 0, 0, 1]
  continuous_toFun := stdSimplex.continuous_map _

/-- [definition] A section retaining the two segment endpoints inside the tetrahedron. -/
def segmentToTetrahedron : C(Segment, Tetrahedron) where
  toFun := stdSimplex.map ![0, 3]
  continuous_toFun := stdSimplex.continuous_map _

/-- [proved-derived; formal-checked] The retained segment is a section of the tetrahedral
collapse. -/
theorem tetrahedronToSegment_comp_section :
    tetrahedronToSegment.comp segmentToTetrahedron = ContinuousMap.id Segment := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map (![0, 0, 0, 1] : Fin 4 → Fin 2)
      (stdSimplex.map (![0, 3] : Fin 2 → Fin 4) point) = point
  rw [stdSimplex.map_comp_apply]
  have hlabels : (![0, 0, 0, 1] : Fin 4 → Fin 2) ∘
      (![0, 3] : Fin 2 → Fin 4) = id := by
    funext index
    fin_cases index <;> rfl
  rw [hlabels]
  exact stdSimplex.map_id_apply point

/-! ## Actual refined edge cells and their globally addressed realization -/

/-- [definition] One supported degree-one occurrence together with one exact edge-word address. -/
abbrev RefinedEdgeCell (chain : SphereChain 1) (scale : ℕ) :=
  (↑(sphereChainSupport 1 chain)) × EdgeWord scale

/-- [definition] The actual refined singular edge carried by one addressed cell. -/
def refinedEdgeSimplex {chain : SphereChain 1} {scale : ℕ}
    (cell : RefinedEdgeCell chain scale) : SphereSingularSimplex 1 :=
  edgeWordSubsimplex cell.2 cell.1.1

/-- [definition] The continuous realization of a refined edge as a degenerate tetrahedral cell. -/
def refinedEdgeRealization {chain : SphereChain 1} {scale : ℕ}
    (cell : RefinedEdgeCell chain scale) :
    C(Tetrahedron, HodgeTwoSphereFundamentalCycle.TwoSphere) :=
  (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 1)) (refinedEdgeSimplex cell)).comp
    tetrahedronToSegment

/-- [definition] The nondegenerate segment realization retained by the edge cell. -/
def refinedEdgeSourceMap {chain : SphereChain 1} {scale : ℕ}
    (cell : RefinedEdgeCell chain scale) :
    C(Segment, HodgeTwoSphereFundamentalCycle.TwoSphere) :=
  TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1)) (refinedEdgeSimplex cell)

/-- [proved-derived; formal-checked] The degenerate cell restricts along its section to the exact
refined singular edge. -/
theorem refinedEdgeRealization_comp_section
    {chain : SphereChain 1} {scale : ℕ} (cell : RefinedEdgeCell chain scale) :
    (refinedEdgeRealization cell).comp segmentToTetrahedron =
      refinedEdgeSourceMap cell := by
  change ((refinedEdgeSourceMap cell).comp tetrahedronToSegment).comp
      segmentToTetrahedron = refinedEdgeSourceMap cell
  rw [ContinuousMap.comp_assoc, tetrahedronToSegment_comp_section]
  exact ContinuousMap.comp_id _

/-- [proved-derived; formal-checked] The tetrahedral presentation and its retained segment have
the same complete receiver range. -/
theorem refinedEdgeRealization_range
    {chain : SphereChain 1} {scale : ℕ} (cell : RefinedEdgeCell chain scale) :
    Set.range (refinedEdgeRealization cell) = Set.range (refinedEdgeSourceMap cell) := by
  apply Set.Subset.antisymm
  · rintro point ⟨source, rfl⟩
    exact ⟨tetrahedronToSegment source, rfl⟩
  · rintro point ⟨source, rfl⟩
    refine ⟨segmentToTetrahedron source, ?_⟩
    simpa only [ContinuousMap.comp_apply] using
      ContinuousMap.congr_fun (refinedEdgeRealization_comp_section cell) source

/-- [definition] Global vertices are actual sphere points at refined-cell tetrahedral vertices. -/
abbrev RefinedEdgeVertex (chain : SphereChain 1) (scale : ℕ) :=
  { point : HodgeTwoSphereFundamentalCycle.TwoSphere //
    ∃ (cell : RefinedEdgeCell chain scale) (index : Fin 4),
      refinedEdgeRealization cell (stdSimplex.vertex index) = point }

/-- [definition] The finite refined edge population as one globally addressed incidence complex. -/
def refinedEdgeComplex (chain : SphereChain 1) (scale : ℕ) :
    AddressedTetrahedralComplex where
  Vertex := RefinedEdgeVertex chain scale
  Cell := RefinedEdgeCell chain scale
  point vertex := vertex.1
  realization := refinedEdgeRealization
  cellVertex cell index :=
    ⟨refinedEdgeRealization cell (stdSimplex.vertex index), ⟨cell, index, rfl⟩⟩
  realizes_vertex _ _ := rfl
  anchorCell vertex := Classical.choose vertex.2
  anchorIndex vertex := Classical.choose (Classical.choose_spec vertex.2)
  anchor_incident vertex := by
    apply Subtype.ext
    exact Classical.choose_spec (Classical.choose_spec vertex.2)

/-! ## Uniform exact scale and coherent labels -/

/-- [proved-derived; formal-checked] Every singular one-chain admits one exact refinement depth
whose complete refined edge population lies in radius-third balls. -/
theorem exists_scale_refinedEdgeCellBallPresentation
    (chain : SphereChain 1) (lebesgue : StarLebesgueLabel) :
    ∃ scale : ℕ,
      Nonempty (CellBallPresentation (refinedEdgeComplex chain scale) lebesgue) := by
  let cover : HodgeTwoSphereFundamentalCycle.TwoSphere →
      Set HodgeTwoSphereFundamentalCycle.TwoSphere :=
    fun center => Metric.ball center (lebesgue.radius / 3)
  have coverOpen : ∀ center, IsOpen (cover center) := fun center =>
    Metric.isOpen_ball
  have coverAll : Set.univ ⊆ ⋃ center, cover center := by
    intro point _
    apply Set.mem_iUnion.2
    refine ⟨point, ?_⟩
    rw [Metric.mem_ball]
    simpa using div_pos lebesgue.radiusPositive (by norm_num : (0 : ℝ) < 3)
  obtain ⟨scale, scaleLaw⟩ :=
    exists_scale_finite_sphereSimplex_family_edge_descendants_subordinate
      (fun occurrence : ↑(sphereChainSupport 1 chain) => occurrence.1)
      cover coverOpen coverAll
  refine ⟨scale, ⟨{
    center := fun cell =>
      Classical.choose
        (scaleLaw cell.1 (edgeWordList cell.2)
          (Nat.le_of_eq (edgeWordList_length cell.2).symm))
    image_carried := ?_ }⟩⟩
  intro cell point pointInRange
  obtain ⟨center, centerLaw⟩ :=
    scaleLaw cell.1 (edgeWordList cell.2)
      (Nat.le_of_eq (edgeWordList_length cell.2).symm)
  have chosenLaw :
      Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 1)) cell.1.1).comp
              (edgeWordMap (edgeWordList cell.2))) ⊆
        cover (Classical.choose
          (scaleLaw cell.1 (edgeWordList cell.2)
            (Nat.le_of_eq (edgeWordList_length cell.2).symm))) :=
    Classical.choose_spec
      (scaleLaw cell.1 (edgeWordList cell.2)
        (Nat.le_of_eq (edgeWordList_length cell.2).symm))
  apply chosenLaw
  rcases pointInRange with ⟨source, rfl⟩
  refine ⟨tetrahedronToSegment source, ?_⟩
  rfl

/-- [proved-derived; formal-checked] The uniformly refined edge population admits one coherent
closed-star label at every globally identified endpoint. -/
theorem exists_scale_refinedEdgeClosedStarLabeling
    (chain : SphereChain 1) (lebesgue : StarLebesgueLabel) :
    ∃ scale : ℕ,
      Nonempty ((refinedEdgeComplex chain scale).ClosedStarLabeling) := by
  obtain ⟨scale, ⟨presentation⟩⟩ :=
    exists_scale_refinedEdgeCellBallPresentation chain lebesgue
  exact ⟨scale, ⟨closedStarLabelingOfCellBalls
    (refinedEdgeComplex chain scale) lebesgue presentation⟩⟩

/-- [definition] Extend coherent finite endpoint labels to all sphere points. -/
def refinedEdgeClosedStarPointLabeling
    {chain : SphereChain 1} {scale : ℕ} (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling) :
    StarPointLabeling := by
  classical
  refine {
    label := fun point =>
      if present : ∃ vertex : (refinedEdgeComplex chain scale).Vertex,
          (refinedEdgeComplex chain scale).point vertex = point then
        labeling.label (Classical.choose present)
      else
        lebesgue.label point
    carried := ?_ }
  intro point
  split_ifs with present
  · let vertex := Classical.choose present
    have pointLaw :
        (refinedEdgeComplex chain scale).point vertex = point :=
      Classical.choose_spec present
    apply labeling.carried vertex
    rw [← pointLaw]
    exact ⟨(refinedEdgeComplex chain scale).anchorCell vertex,
      (refinedEdgeComplex chain scale).anchorIndex vertex,
      (refinedEdgeComplex chain scale).anchor_incident vertex,
      ⟨stdSimplex.vertex
          ((refinedEdgeComplex chain scale).anchorIndex vertex), by
        rw [(refinedEdgeComplex chain scale).realizes_vertex,
          (refinedEdgeComplex chain scale).anchor_incident]⟩⟩
  · apply lebesgue.ball_carried point
    rw [Metric.mem_ball, dist_self]
    exact lebesgue.radiusPositive

/-- [proved-derived; formal-checked] The global edge labeling returns the coherent finite label at
every actual refined vertex. -/
theorem refinedEdgeClosedStarPointLabeling_vertex
    {chain : SphereChain 1} {scale : ℕ} (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling)
    (vertex : (refinedEdgeComplex chain scale).Vertex) :
    (refinedEdgeClosedStarPointLabeling lebesgue labeling).label
        ((refinedEdgeComplex chain scale).point vertex) =
      labeling.label vertex := by
  classical
  simp only [refinedEdgeClosedStarPointLabeling]
  split_ifs with present
  · have hvertex : Classical.choose present = vertex := by
      apply Subtype.ext
      exact (Classical.choose_spec present).trans rfl
    rw [hvertex]
  · exact False.elim (present ⟨vertex, rfl⟩)

/-- [proved-derived; formal-checked] Every point of a refined edge cell lies in each of the four
open stars selected by its globally addressed degenerate tetrahedral vertices. -/
theorem refinedEdgeCell_range_carried
    {chain : SphereChain 1} {scale : ℕ} (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling)
    (cell : (refinedEdgeComplex chain scale).Cell)
    (index : Fin 4) :
    Set.range ((refinedEdgeComplex chain scale).realization cell) ⊆
      vertexStar
        ((refinedEdgeClosedStarPointLabeling lebesgue labeling).label
          ((refinedEdgeComplex chain scale).point
            ((refinedEdgeComplex chain scale).cellVertex cell index))) := by
  rw [refinedEdgeClosedStarPointLabeling_vertex lebesgue labeling
    ((refinedEdgeComplex chain scale).cellVertex cell index)]
  intro point pointInRange
  apply labeling.carried
    ((refinedEdgeComplex chain scale).cellVertex cell index)
  exact ⟨cell, index, rfl, pointInRange⟩

section Audit

#print axioms tetrahedronToSegment_comp_section
#print axioms refinedEdgeRealization_comp_section
#print axioms refinedEdgeRealization_range
#print axioms exists_scale_refinedEdgeCellBallPresentation
#print axioms exists_scale_refinedEdgeClosedStarLabeling
#print axioms refinedEdgeClosedStarPointLabeling_vertex
#print axioms refinedEdgeCell_range_carried

end Audit

end Soma.Holonics.Millennium.HodgeRefinedEdgeClosedStar
