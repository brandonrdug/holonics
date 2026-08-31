import ElementaryHolonics.Millennium.HodgeBarycentricTetrahedronCoverSmallness
import ElementaryHolonics.Millennium.HodgeTetrahedralStarCover

/-!
# Finite closed-star labels for the Hodge boundary witness

Cell-local labels do not preserve a shared face.  The correct carrier owns one global vertex
population and lets every incident tetrahedron refer to that same vertex.  A closed-star label says
that the complete image of every cell incident to a vertex lies in the open tetrahedral star named
by that vertex.  Consequently any point of a cell belongs simultaneously to the four stars named
by its four vertices, and the empty fourfold intersection supplies the degree-three admissibility
law.

The metric constructor is exact.  A Lebesgue radius for the four target stars is divided into
three distinct transport legs: point-to-cell centre, cell-centre-to-shared-vertex, and
shared-vertex-to-anchor-centre.  No floating radius, nearest-neighbour heuristic, or cell-local
label choice occurs.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the imported exact open-star cover and metric
Lebesgue-number theorem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling

set_option maxHeartbeats 2000000

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision

/-- [definition] One addressed tetrahedral occurrence complex with globally identified vertices.
`anchorCell` and `anchorIndex` retain one actual incident occurrence for every vertex; they are
reconstruction data, not a choice-defined decoder from a quotient. -/
structure AddressedTetrahedralComplex where
  Vertex : Type*
  Cell : Type*
  point : Vertex → HodgeTwoSphereFundamentalCycle.TwoSphere
  realization : Cell → C(Tetrahedron, HodgeTwoSphereFundamentalCycle.TwoSphere)
  cellVertex : Cell → Fin 4 → Vertex
  realizes_vertex : ∀ cell index,
    realization cell (stdSimplex.vertex index) = point (cellVertex cell index)
  anchorCell : Vertex → Cell
  anchorIndex : Vertex → Fin 4
  anchor_incident : ∀ vertex,
    cellVertex (anchorCell vertex) (anchorIndex vertex) = vertex

namespace AddressedTetrahedralComplex

/-- [definition] Complete target image of every cell incident to one global vertex. -/
def closedStarImage (complex : AddressedTetrahedralComplex)
    (vertex : complex.Vertex) : Set HodgeTwoSphereFundamentalCycle.TwoSphere :=
  {point | ∃ cell index,
    complex.cellVertex cell index = vertex ∧
      point ∈ Set.range (complex.realization cell)}

/-- [definition] One label per global vertex, with the whole incident closed star carried by the
named target-star aperture. -/
structure ClosedStarLabeling (complex : AddressedTetrahedralComplex) where
  label : complex.Vertex → TetraVertex
  carried : ∀ vertex,
    complex.closedStarImage vertex ⊆ vertexStar (label vertex)

namespace ClosedStarLabeling

/-- [proved-derived; formal-checked] Every cell of a closed-star-labelled complex has an actual
common target point in all four named stars. -/
theorem commonStarAtCell {complex : AddressedTetrahedralComplex}
    (labeling : complex.ClosedStarLabeling) (cell : complex.Cell) :
    ∃ point : HodgeTwoSphereFundamentalCycle.TwoSphere,
      ∀ index : Fin 4,
        point ∈ vertexStar (labeling.label (complex.cellVertex cell index)) := by
  refine ⟨complex.realization cell tetrahedronBarycenter, fun index => ?_⟩
  apply labeling.carried (complex.cellVertex cell index)
  exact ⟨cell, index, rfl, ⟨tetrahedronBarycenter, rfl⟩⟩

/-- [proved-derived; formal-checked] Closed-star incidence supplies the exact four-label
admissibility law consumed by the finite tetrahedral face current. -/
theorem fourLabelsAdmissibleAtCell {complex : AddressedTetrahedralComplex}
    (labeling : complex.ClosedStarLabeling) (cell : complex.Cell) :
    FourLabelsAdmissible
      (labeling.label (complex.cellVertex cell 0))
      (labeling.label (complex.cellVertex cell 1))
      (labeling.label (complex.cellVertex cell 2))
      (labeling.label (complex.cellVertex cell 3)) := by
  obtain ⟨point, common⟩ := labeling.commonStarAtCell cell
  exact fourLabelsAdmissible_of_commonStarPoint
    (fun index => labeling.label (complex.cellVertex cell index)) point common

end ClosedStarLabeling

end AddressedTetrahedralComplex

/-- [definition] A uniform exact Lebesgue aperture for the tetrahedral star cover, together with
one coarse star label at every sphere point. -/
structure StarLebesgueLabel where
  radius : ℝ
  radiusPositive : 0 < radius
  label : HodgeTwoSphereFundamentalCycle.TwoSphere → TetraVertex
  ball_carried : ∀ point,
    Metric.ball point radius ⊆ vertexStar (label point)

/-- [proved-derived; formal-checked] Compactness of the sphere and the exact four-star cover
construct a positive uniform aperture and a retained star choice at every point. -/
theorem exists_starLebesgueLabel : Nonempty StarLebesgueLabel := by
  obtain ⟨radius, radiusPositive, ballRefines⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ
      isOpen_vertexStar vertexStar_cover
  choose label labelLaw using fun point => ballRefines point (Set.mem_univ point)
  exact ⟨{
    radius := radius
    radiusPositive := radiusPositive
    label := label
    ball_carried := labelLaw }⟩

/-- [definition] A radius-third ball carrying every cell image.  The centre remains attached to
the addressed cell as incidence testimony. -/
structure CellBallPresentation (complex : AddressedTetrahedralComplex)
    (lebesgue : StarLebesgueLabel) where
  center : complex.Cell → HodgeTwoSphereFundamentalCycle.TwoSphere
  image_carried : ∀ cell,
    Set.range (complex.realization cell) ⊆
      Metric.ball (center cell) (lebesgue.radius / 3)

/-- [proved-derived; formal-checked] Three exact radius-third legs transport every incident cell
image into the coarse star selected at the global vertex's anchor cell. -/
def closedStarLabelingOfCellBalls
    (complex : AddressedTetrahedralComplex) (lebesgue : StarLebesgueLabel)
    (presentation : CellBallPresentation complex lebesgue) :
    complex.ClosedStarLabeling where
  label vertex := lebesgue.label (presentation.center (complex.anchorCell vertex))
  carried := by
    intro vertex point pointInClosedStar
    rcases pointInClosedStar with ⟨cell, index, vertexLaw, pointInCell⟩
    apply lebesgue.ball_carried (presentation.center (complex.anchorCell vertex))
    rw [Metric.mem_ball]
    have pointToCellCenter := presentation.image_carried cell pointInCell
    have vertexInCellRange : complex.point vertex ∈ Set.range (complex.realization cell) := by
      refine ⟨stdSimplex.vertex index, ?_⟩
      rw [complex.realizes_vertex, vertexLaw]
    have vertexToCellCenter := presentation.image_carried cell vertexInCellRange
    have anchorVertexInRange :
        complex.point vertex ∈
          Set.range (complex.realization (complex.anchorCell vertex)) := by
      refine ⟨stdSimplex.vertex (complex.anchorIndex vertex), ?_⟩
      rw [complex.realizes_vertex, complex.anchor_incident]
    have vertexToAnchorCenter :=
      presentation.image_carried (complex.anchorCell vertex) anchorVertexInRange
    rw [Metric.mem_ball] at pointToCellCenter vertexToCellCenter vertexToAnchorCenter
    calc
      dist point (presentation.center (complex.anchorCell vertex)) ≤
          dist point (presentation.center cell) +
            dist (presentation.center cell) (complex.point vertex) +
            dist (complex.point vertex)
              (presentation.center (complex.anchorCell vertex)) := by
        calc
          dist point (presentation.center (complex.anchorCell vertex)) ≤
              dist point (presentation.center cell) +
                dist (presentation.center cell)
                  (presentation.center (complex.anchorCell vertex)) :=
            dist_triangle _ _ _
          _ ≤ dist point (presentation.center cell) +
                (dist (presentation.center cell) (complex.point vertex) +
                  dist (complex.point vertex)
                    (presentation.center (complex.anchorCell vertex))) := by
            exact add_le_add_right
              (dist_triangle (presentation.center cell) (complex.point vertex)
                (presentation.center (complex.anchorCell vertex))) _
          _ = _ := by ring
      _ < lebesgue.radius := by
        rw [dist_comm (presentation.center cell) (complex.point vertex)]
        linarith

section Audit

#print axioms AddressedTetrahedralComplex.ClosedStarLabeling.commonStarAtCell
#print axioms AddressedTetrahedralComplex.ClosedStarLabeling.fourLabelsAdmissibleAtCell
#print axioms exists_starLebesgueLabel
#print axioms closedStarLabelingOfCellBalls

end Audit

end Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
