import ElementaryHolonics.Millennium.HodgeRefinedCycleCarrier
import ElementaryHolonics.Millennium.HodgeFiniteClosedStarLabeling

/-!
# Closed-star incidence for the finite refined triangle population

The degree-three boundary obstruction already owns a globally addressed tetrahedral occurrence
complex.  Surjectivity in degree two needs the corresponding owner for the actual finite support
of one singular two-chain.  Each fixed-depth refined triangle is presented as a degenerate
tetrahedron, but its vertices are identified by their actual sphere point rather than by the local
copy in which they occur.  The existing radius-third closed-star constructor can therefore label
the complete incident population coherently.

This file constructs that incidence and its uniform scale.  It does not yet construct the
common-star singular homotopy from the refined source current to the radial face realization.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the actual singular-chain support,
exact refinement words, metric cover smallness, and the existing closed-star constructor.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRefinedTriangleClosedStar

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricChainSupport
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgePointCarry

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- [definition] One genuinely supported source triangle together with one retained fixed-depth
refinement word. -/
abbrev RefinedTriangleCell (chain : SphereChain 2) (scale : ℕ) :=
  (↑(sphereChainSupport 2 chain)) × TriangleWord scale

/-- [definition] The addressed refined singular triangle carried by one occurrence word. -/
def refinedTriangleSimplex {chain : SphereChain 2} {scale : ℕ}
    (cell : RefinedTriangleCell chain scale) : SphereSingularSimplex 2 :=
  triangleWordSubsimplex cell.2 cell.1.1

/-- [definition] The standard codegeneracy collapsing a tetrahedron to a triangle. -/
def tetrahedronToTriangle : C(Tetrahedron, Triangle) where
  toFun := stdSimplex.map (SimplexCategory.σ (0 : Fin 3)).toOrderHom
  continuous_toFun := stdSimplex.continuous_map _

/-- [definition] The triangle occurrence viewed as a degenerate tetrahedral occurrence so the
standing global-vertex closed-star owner can be reused without a second labeling ontology. -/
def refinedTriangleRealization {chain : SphereChain 2} {scale : ℕ}
    (cell : RefinedTriangleCell chain scale) :
    C(Tetrahedron, HodgeTwoSphereFundamentalCycle.TwoSphere) :=
  (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2)) (refinedTriangleSimplex cell)).comp
    tetrahedronToTriangle

/-- [definition] Global vertices are actual sphere points occurring at refined cell vertices.
Local copies at seams therefore become definitionally the same addressed vertex. -/
abbrev RefinedTriangleVertex (chain : SphereChain 2) (scale : ℕ) :=
  { point : HodgeTwoSphereFundamentalCycle.TwoSphere //
    ∃ (cell : RefinedTriangleCell chain scale) (index : Fin 4),
      refinedTriangleRealization cell (stdSimplex.vertex index) = point }

/-- [definition] The finite refined triangle population as one
globally addressed incidence complex. -/
def refinedTriangleComplex (chain : SphereChain 2) (scale : ℕ) :
    AddressedTetrahedralComplex where
  Vertex := RefinedTriangleVertex chain scale
  Cell := RefinedTriangleCell chain scale
  point vertex := vertex.1
  realization := refinedTriangleRealization
  cellVertex cell index :=
    ⟨refinedTriangleRealization cell (stdSimplex.vertex index), ⟨cell, index, rfl⟩⟩
  realizes_vertex _ _ := rfl
  anchorCell vertex := Classical.choose vertex.2
  anchorIndex vertex := Classical.choose (Classical.choose_spec vertex.2)
  anchor_incident vertex := by
    apply Subtype.ext
    exact Classical.choose_spec (Classical.choose_spec vertex.2)

/-- [proved-derived; formal-checked] Every actual singular two-chain has one exact
refinement depth whose globally addressed refined triangle complex admits a radius-third cell-ball
presentation. -/
theorem exists_scale_refinedTriangleCellBallPresentation
    (chain : SphereChain 2) (lebesgue : StarLebesgueLabel) :
    ∃ scale : ℕ,
      Nonempty (CellBallPresentation (refinedTriangleComplex chain scale) lebesgue) := by
  let cover : HodgeTwoSphereFundamentalCycle.TwoSphere →
      Set HodgeTwoSphereFundamentalCycle.TwoSphere :=
    fun center => Metric.ball center (lebesgue.radius / 3)
  have coverOpen : ∀ center, IsOpen (cover center) :=
    fun center => Metric.isOpen_ball
  have coverAll : Set.univ ⊆ ⋃ center, cover center := by
    intro point _
    apply Set.mem_iUnion.2
    refine ⟨point, ?_⟩
    rw [Metric.mem_ball]
    simpa using div_pos lebesgue.radiusPositive (by norm_num : (0 : ℝ) < 3)
  obtain ⟨scale, scaleLaw⟩ :=
    exists_scale_chain_support_barycentric_descendants_subordinate
      chain cover coverOpen coverAll
  refine ⟨scale, ⟨{
    center := fun cell =>
      Classical.choose
        (scaleLaw cell.1 (triangleWordList cell.2)
          (Nat.le_of_eq (triangleWordList_length cell.2).symm))
    image_carried := ?_ }⟩⟩
  intro cell point pointInRange
  obtain ⟨center, centerLaw⟩ :=
    scaleLaw cell.1 (triangleWordList cell.2)
      (Nat.le_of_eq (triangleWordList_length cell.2).symm)
  have chosenLaw :
      Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 2)) cell.1.1).comp
              (barycentricTriangleWordMap (triangleWordList cell.2))) ⊆
        cover (Classical.choose
          (scaleLaw cell.1 (triangleWordList cell.2)
            (Nat.le_of_eq (triangleWordList_length cell.2).symm))) :=
    Classical.choose_spec
      (scaleLaw cell.1 (triangleWordList cell.2)
        (Nat.le_of_eq (triangleWordList_length cell.2).symm))
  apply chosenLaw
  rcases pointInRange with ⟨source, rfl⟩
  refine ⟨tetrahedronToTriangle source, ?_⟩
  rfl

/-- [proved-derived; formal-checked] Every actual singular two-chain therefore has
one fixed refinement whose complete incident triangle population carries one coherent closed-star
label per actual sphere vertex. -/
theorem exists_scale_refinedTriangleClosedStarLabeling
    (chain : SphereChain 2) (lebesgue : StarLebesgueLabel) :
    ∃ scale : ℕ,
      Nonempty ((refinedTriangleComplex chain scale).ClosedStarLabeling) := by
  obtain ⟨scale, ⟨presentation⟩⟩ :=
    exists_scale_refinedTriangleCellBallPresentation chain lebesgue
  exact ⟨scale, ⟨closedStarLabelingOfCellBalls
    (refinedTriangleComplex chain scale) lebesgue presentation⟩⟩

/-- [definition] Extend the coherent labels on the finite refined vertex population to all sphere
points.  Points outside that population retain the standing Lebesgue-star label. -/
def refinedClosedStarPointLabeling
    {chain : SphereChain 2} {scale : ℕ} (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling) :
    StarPointLabeling := by
  classical
  refine {
    label := fun point =>
      if present : ∃ vertex : (refinedTriangleComplex chain scale).Vertex,
          (refinedTriangleComplex chain scale).point vertex = point then
        labeling.label (Classical.choose present)
      else
        lebesgue.label point
    carried := ?_ }
  intro point
  split_ifs with present
  · let vertex := Classical.choose present
    have pointLaw :
        (refinedTriangleComplex chain scale).point vertex = point :=
      Classical.choose_spec present
    apply labeling.carried vertex
    rw [← pointLaw]
    exact ⟨(refinedTriangleComplex chain scale).anchorCell vertex,
      (refinedTriangleComplex chain scale).anchorIndex vertex,
      (refinedTriangleComplex chain scale).anchor_incident vertex,
      ⟨stdSimplex.vertex
          ((refinedTriangleComplex chain scale).anchorIndex vertex), by
        rw [(refinedTriangleComplex chain scale).realizes_vertex,
          (refinedTriangleComplex chain scale).anchor_incident]⟩⟩
  · apply lebesgue.ball_carried point
    rw [Metric.mem_ball, dist_self]
    exact lebesgue.radiusPositive

/-- [proved-derived; formal-checked] The global extension returns exactly the coherent finite label
at every actual refined vertex; no local copy can select a different label. -/
theorem refinedClosedStarPointLabeling_vertex
    {chain : SphereChain 2} {scale : ℕ} (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (vertex : (refinedTriangleComplex chain scale).Vertex) :
    (refinedClosedStarPointLabeling lebesgue labeling).label
        ((refinedTriangleComplex chain scale).point vertex) =
      labeling.label vertex := by
  classical
  simp only [refinedClosedStarPointLabeling]
  split_ifs with present
  · congr 1
    apply Subtype.ext
    exact (Classical.choose_spec present).trans rfl
  · exact False.elim (present ⟨vertex, rfl⟩)

/-- [proved-derived; formal-checked] Every point of a refined triangle cell lies simultaneously in
the target stars named by all four of its degenerate tetrahedral vertex occurrences. -/
theorem refinedTriangleCell_range_carried
    {chain : SphereChain 2} {scale : ℕ} (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (cell : (refinedTriangleComplex chain scale).Cell)
    (index : Fin 4) :
    Set.range ((refinedTriangleComplex chain scale).realization cell) ⊆
      vertexStar
        ((refinedClosedStarPointLabeling lebesgue labeling).label
          ((refinedTriangleComplex chain scale).point
            ((refinedTriangleComplex chain scale).cellVertex cell index))) := by
  rw [refinedClosedStarPointLabeling_vertex lebesgue labeling
    ((refinedTriangleComplex chain scale).cellVertex cell index)]
  intro point pointInRange
  apply labeling.carried
    ((refinedTriangleComplex chain scale).cellVertex cell index)
  exact ⟨cell, index, rfl, pointInRange⟩

section Audit

#print axioms refinedTriangleComplex
#print axioms exists_scale_refinedTriangleCellBallPresentation
#print axioms exists_scale_refinedTriangleClosedStarLabeling
#print axioms refinedClosedStarPointLabeling_vertex
#print axioms refinedTriangleCell_range_carried

end Audit

end Soma.Holonics.Millennium.HodgeRefinedTriangleClosedStar
