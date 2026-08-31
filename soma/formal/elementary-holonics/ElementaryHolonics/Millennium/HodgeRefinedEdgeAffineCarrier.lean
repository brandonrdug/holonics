import ElementaryHolonics.Millennium.HodgeRefinedEdgeClosedStar
import ElementaryHolonics.Millennium.HodgeCommonStarAffineCarrier

/-!
# Uniform common-star affine carriers on an actual singular one-chain

One exact refinement depth and one coherent closed-star labeling turn every addressed refined
edge into a `CommonStarEdge`.  The two carrier labels are read at the actual segment endpoints,
not from parent copies.  Consequently the complete affine endpoint path is natural under every
shared endpoint incidence.

Truth status: definitions are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the exact refined-edge closed-star carrier and the
degree-one common-star homotopy.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRefinedEdgeAffineCarrier

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set Topology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgePointCarry
open Soma.Holonics.Millennium.HodgeRefinedEdgeClosedStar
open Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- [definition] The two nonduplicated tetrahedral vertices presenting the segment endpoints. -/
def segmentEndpointTetraVertex : Fin 2 → Fin 4 := ![0, 3]

/-- [proved-derived; formal-checked] The selected tetrahedral vertices realize the corresponding
actual refined segment endpoints. -/
theorem refinedEdgeRealization_endpoint
    {chain : SphereChain 1} {scale : ℕ}
    (cell : RefinedEdgeCell chain scale) (index : Fin 2) :
    refinedEdgeRealization cell
        (stdSimplex.vertex (segmentEndpointTetraVertex index)) =
      refinedEdgeSourceMap cell (stdSimplex.vertex index) := by
  change refinedEdgeSourceMap cell
      (tetrahedronToSegment
        (stdSimplex.vertex (segmentEndpointTetraVertex index))) = _
  change refinedEdgeSourceMap cell
      (stdSimplex.map (![0, 0, 0, 1] : Fin 4 → Fin 2)
        (stdSimplex.vertex (segmentEndpointTetraVertex index))) = _
  rw [stdSimplex.map_vertex]
  congr 2
  fin_cases index <;> rfl

/-- [definition] Coherent labels at the two actual endpoints of one refined edge. -/
def refinedEdgeLabels {chain : SphereChain 1} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling)
    (cell : RefinedEdgeCell chain scale) :
    Fin 2 → HodgeTetrahedralChainComplex.TetraVertex :=
  fun index =>
    (refinedEdgeClosedStarPointLabeling lebesgue labeling).label
      ((refinedEdgeComplex chain scale).point
        ((refinedEdgeComplex chain scale).cellVertex cell
          (segmentEndpointTetraVertex index)))

/-- [proved-derived; formal-checked] Each edge label is the global point-label of the actual
singular endpoint. -/
theorem refinedEdgeLabels_endpoint
    {chain : SphereChain 1} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling)
    (cell : RefinedEdgeCell chain scale) (index : Fin 2) :
    refinedEdgeLabels lebesgue labeling cell index =
      (refinedEdgeClosedStarPointLabeling lebesgue labeling).label
        (refinedEdgeSourceMap cell (stdSimplex.vertex index)) := by
  change (refinedEdgeClosedStarPointLabeling lebesgue labeling).label
      (refinedEdgeRealization cell
        (stdSimplex.vertex (segmentEndpointTetraVertex index))) = _
  rw [refinedEdgeRealization_endpoint]

/-- [proved-derived; formal-checked] The ordered endpoint word agrees with the standing
point-natural singular-simplex label word. -/
theorem refinedEdgeLabels_eq_simplexPointLabels
    {chain : SphereChain 1} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling)
    (cell : RefinedEdgeCell chain scale) :
    refinedEdgeLabels lebesgue labeling cell =
      simplexPointLabels
        (refinedEdgeClosedStarPointLabeling lebesgue labeling)
        (refinedEdgeSimplex cell) := by
  funext index
  rw [refinedEdgeLabels_endpoint]
  rfl

/-- [proved-derived; formal-checked] The complete edge image lies in both endpoint-label stars. -/
theorem refinedEdgeSourceMap_carried
    {chain : SphereChain 1} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling)
    (cell : RefinedEdgeCell chain scale)
    (point : Segment) (index : Fin 2) :
    refinedEdgeSourceMap cell point ∈
      HodgeTetrahedralStarCover.vertexStar
        (refinedEdgeLabels lebesgue labeling cell index) := by
  apply refinedEdgeCell_range_carried lebesgue labeling cell
    (segmentEndpointTetraVertex index)
  refine ⟨segmentToTetrahedron point, ?_⟩
  change refinedEdgeRealization cell (segmentToTetrahedron point) =
    refinedEdgeSourceMap cell point
  simpa only [ContinuousMap.comp_apply] using
    ContinuousMap.congr_fun (refinedEdgeRealization_comp_section cell) point

/-- [definition] The common-star affine carrier of one actual refined edge cell. -/
def refinedEdgeCommonStarCarrier
    {chain : SphereChain 1} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling)
    (cell : RefinedEdgeCell chain scale) :
      Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier.CommonStarEdge where
  source := refinedEdgeSourceMap cell
  labels := refinedEdgeLabels lebesgue labeling cell
  carried := refinedEdgeSourceMap_carried lebesgue labeling cell

/-- [definition] One fixed scale, one coherent labeling, and the resulting common-star carrier
on every addressed refined edge occurrence. -/
structure RefinedEdgeAffineCarrierFamily (chain : SphereChain 1)
    (lebesgue : StarLebesgueLabel) where
  scale : ℕ
  labeling : (refinedEdgeComplex chain scale).ClosedStarLabeling
  carrier : (refinedEdgeComplex chain scale).Cell →
    Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier.CommonStarEdge
  carrier_eq : carrier = refinedEdgeCommonStarCarrier lebesgue labeling

/-- [proved-derived; formal-checked] Every singular one-chain admits one uniform family of exact
degree-one common-star carriers. -/
theorem nonempty_refinedEdgeAffineCarrierFamily
    (chain : SphereChain 1) (lebesgue : StarLebesgueLabel) :
    Nonempty (RefinedEdgeAffineCarrierFamily chain lebesgue) := by
  obtain ⟨scale, ⟨labeling⟩⟩ :=
    exists_scale_refinedEdgeClosedStarLabeling chain lebesgue
  exact ⟨{
    scale := scale
    labeling := labeling
    carrier := refinedEdgeCommonStarCarrier lebesgue labeling
    carrier_eq := rfl }⟩

/-- [proved-derived; formal-checked] Every carrier starts at the exact refined source edge. -/
theorem RefinedEdgeAffineCarrierFamily.homotopy_zero
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (cell : (refinedEdgeComplex chain family.scale).Cell)
    (point : Segment) :
    (family.carrier cell).affineSphereHomotopy (0, point) =
      refinedEdgeSourceMap cell point := by
  rw [family.carrier_eq]
  exact CommonStarEdge.affineSphereHomotopy_zero _ _

/-- [proved-derived; formal-checked] Every carrier ends at the raw ordered affine-label edge. -/
theorem RefinedEdgeAffineCarrierFamily.homotopy_one
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (cell : (refinedEdgeComplex chain family.scale).Cell)
    (point : Segment) :
    (family.carrier cell).affineSphereHomotopy (1, point) =
      lowLabelSphereMap 1 (by omega)
        (refinedEdgeLabels lebesgue family.labeling cell) point := by
  rw [family.carrier_eq]
  exact CommonStarEdge.affineSphereHomotopy_one _ _

/-- [proved-derived; formal-checked] Shared actual endpoints induce equal complete vertical
homotopy paths.  The equality uses the global point-label, not an endpoint-only sign quotient. -/
theorem RefinedEdgeAffineCarrierFamily.homotopy_vertex_congr
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (first second : (refinedEdgeComplex chain family.scale).Cell)
    (firstVertex secondVertex : Fin 2)
    (sourceLaw : refinedEdgeSourceMap first (stdSimplex.vertex firstVertex) =
      refinedEdgeSourceMap second (stdSimplex.vertex secondVertex))
    (time : unitInterval) :
    (family.carrier first).affineSphereHomotopy
        (time, stdSimplex.vertex firstVertex) =
      (family.carrier second).affineSphereHomotopy
        (time, stdSimplex.vertex secondVertex) := by
  rw [family.carrier_eq]
  apply CommonStarEdge.affineSphereHomotopy_vertex_congr
  · exact sourceLaw
  · simp only [refinedEdgeCommonStarCarrier]
    rw [refinedEdgeLabels_endpoint, refinedEdgeLabels_endpoint, sourceLaw]

section Audit

#print axioms refinedEdgeRealization_endpoint
#print axioms refinedEdgeLabels_eq_simplexPointLabels
#print axioms refinedEdgeSourceMap_carried
#print axioms nonempty_refinedEdgeAffineCarrierFamily
#print axioms RefinedEdgeAffineCarrierFamily.homotopy_zero
#print axioms RefinedEdgeAffineCarrierFamily.homotopy_one
#print axioms RefinedEdgeAffineCarrierFamily.homotopy_vertex_congr

end Audit

end Soma.Holonics.Millennium.HodgeRefinedEdgeAffineCarrier
