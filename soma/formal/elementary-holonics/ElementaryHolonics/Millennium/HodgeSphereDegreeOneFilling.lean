import ElementaryHolonics.Millennium.HodgeRefinedEdgeAffineCarrier
import ElementaryHolonics.Millennium.HodgeTriangleHomotopyPrism
import ElementaryHolonics.Millennium.HodgeBarycentricSubdivisionHomotopy
import ElementaryHolonics.Millennium.HodgeRadialCurrent
import ElementaryHolonics.Millennium.HodgeIteratedBarycentricHomology

/-!
# Exact degree-one filling on the two-sphere

This file composes the already returned local owners rather than founding another carrier.  A
finite singular one-current is uniformly refined, transported through its common-star affine
edge prisms, normalized to the finite tetrahedral edge complex, filled there, and transported
back.  Every intermediate chain and every endpoint path remains explicit.

Truth status: definitions are `[definition]`; checked identities are
`[proved-derived; formal-checked]` relative to the imported exact singular-chain, subdivision,
common-star, prism, point-carry, and tetrahedral realization laws.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereDegreeOneFilling

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricSubdivisionHomotopy
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeBarycentricChainSupport
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgePointCarry
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralRealizationChainMap
open Soma.Holonics.Millennium.HodgeRadialCurrent
open Soma.Holonics.Millennium.HodgeTriangleHomotopyPrism
open Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier
open Soma.Holonics.Millennium.HodgeRefinedEdgeClosedStar
open Soma.Holonics.Millennium.HodgeRefinedEdgeAffineCarrier

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-! ## Exact transport from a chain to any fixed refinement depth -/

/-- [definition] The accumulated retained prism from a one-chain to its iterated barycentric
refinement. -/
def iteratedEdgeSubdivisionHomotopy : ℕ → SphereChain 1 → SphereChain 2
  | 0 => fun _ => 0
  | scale + 1 => fun chain =>
      barycentricEdgeSubdivisionHomotopyMorphism
          (iteratedBarycentricEdgeSubdivision scale chain) +
        iteratedEdgeSubdivisionHomotopy scale chain

/-- [proved-derived; formal-checked] The accumulated prism returns exactly the refined current
minus its unrefined source. -/
theorem boundary_iteratedEdgeSubdivisionHomotopy
    (scale : ℕ) (chain : SphereChain 1) :
    SphereSingularChainComplex.d 2 1
        (iteratedEdgeSubdivisionHomotopy scale chain) =
      iteratedBarycentricEdgeSubdivision scale chain - chain := by
  induction scale with
  | zero =>
      simp [iteratedEdgeSubdivisionHomotopy, iteratedBarycentricEdgeSubdivision]
  | succ scale inductionHypothesis =>
      rw [iteratedEdgeSubdivisionHomotopy, map_add, inductionHypothesis]
      have oneStep := congrArg
        (fun morphism : SphereSingularChainComplex.X 1 ⟶
            SphereSingularChainComplex.X 1 =>
          morphism (iteratedBarycentricEdgeSubdivision scale chain))
        barycentricEdgeSubdivisionHomotopyMorphism_comp_boundary
      simp only [ConcreteCategory.comp_apply] at oneStep
      change SphereSingularChainComplex.d 2 1
          (barycentricEdgeSubdivisionHomotopyMorphism
            (iteratedBarycentricEdgeSubdivision scale chain)) =
        barycentricEdgeSubdivisionMorphism
            (iteratedBarycentricEdgeSubdivision scale chain) -
          iteratedBarycentricEdgeSubdivision scale chain at oneStep
      rw [oneStep, iteratedBarycentricEdgeSubdivision]
      module

/-! ## The actual finite refined edge population -/

/-- [definition] Exact rational weight of one addressed refined edge descendant. -/
def refinedEdgeCoefficient {chain : SphereChain 1} {scale : ℕ}
    (cell : RefinedEdgeCell chain scale) : ℚ :=
  sphereChainCoefficient 1 chain cell.1.1 * edgeWordSign cell.2

/-- [proved-derived; formal-checked] The complete addressed refined-edge population reconstructs
the fixed-depth subdivision exactly. -/
theorem sum_refinedEdgeCoefficient_simplexGenerator
    (chain : SphereChain 1) (scale : ℕ) :
    (∑ cell : RefinedEdgeCell chain scale,
      refinedEdgeCoefficient cell • simplexGenerator (refinedEdgeSimplex cell)) =
      iteratedBarycentricEdgeSubdivision scale chain := by
  classical
  have supportReconstruction :
      (∑ source : ↑(sphereChainSupport 1 chain),
        sphereChainCoefficient 1 chain source.1 • simplexGenerator source.1) = chain := by
    have reconstruction :=
      sum_support_sphereChainCoefficient_simplexGenerator 1 chain
    rw [← Finset.sum_attach, Finset.attach_eq_univ] at reconstruction
    exact reconstruction
  calc
    (∑ cell : RefinedEdgeCell chain scale,
        refinedEdgeCoefficient cell • simplexGenerator (refinedEdgeSimplex cell)) =
      ∑ source : ↑(sphereChainSupport 1 chain), ∑ word : EdgeWord scale,
        (sphereChainCoefficient 1 chain source.1 * edgeWordSign word) •
          simplexGenerator (edgeWordSubsimplex word source.1) := by
            rw [Fintype.sum_prod_type]
            simp only [refinedEdgeCoefficient, refinedEdgeSimplex]
    _ = ∑ source : ↑(sphereChainSupport 1 chain),
        iteratedBarycentricEdgeSubdivision scale
          (sphereChainCoefficient 1 chain source.1 • simplexGenerator source.1) := by
      apply Fintype.sum_congr _ _
      intro source
      rw [iteratedBarycentricEdgeSubdivision_smul,
        edgeWordExpansion, Finset.smul_sum]
      simp only [mul_smul]
    _ = iteratedBarycentricEdgeSubdivision scale
        (∑ source : ↑(sphereChainSupport 1 chain),
          sphereChainCoefficient 1 chain source.1 • simplexGenerator source.1) := by
      symm
      induction (Finset.univ : Finset ↑(sphereChainSupport 1 chain)) using
          Finset.induction_on with
      | empty =>
          exact Soma.Holonics.Millennium.HodgeIteratedBarycentricHomology.iteratedBarycentricEdgeSubdivision_zero scale
      | @insert source sources absent inductionHypothesis =>
          rw [Finset.sum_insert absent, Finset.sum_insert absent,
            iteratedBarycentricEdgeSubdivision_add, inductionHypothesis]
    _ = iteratedBarycentricEdgeSubdivision scale chain := by
      rw [supportReconstruction]

/-! ## Point-natural descent of every vertical endpoint path -/

/-- [definition] The constant addressed edge at one actual sphere point. -/
def constantPointEdge
    (point : HodgeTwoSphereFundamentalCycle.TwoSphere) :
    C(Segment, HodgeTwoSphereFundamentalCycle.TwoSphere) where
  toFun := fun _ => point
  continuous_toFun := continuous_const

/-- [definition] A point-natural common-star carrier.  Both endpoint occurrences retain the same
actual point and the same globally selected label. -/
def pointCommonStarEdge (labeling : StarPointLabeling)
    (point : HodgeTwoSphereFundamentalCycle.TwoSphere) : CommonStarEdge where
  source := constantPointEdge point
  labels := fun _ => labeling.label point
  carried := fun _ _ => labeling.carried point

/-- [definition] The canonical vertical affine path from an actual sphere point to its selected
tetrahedral label. -/
def pointEndpointPath (labeling : StarPointLabeling)
    (point : HodgeTwoSphereFundamentalCycle.TwoSphere) :
    SphereSingularSimplex 1 :=
  edgeHomotopyVertexSimplex
    (pointCommonStarEdge labeling point).affineSphereHomotopy 0

/-- [definition] Coproduct-linear extension of the canonical endpoint path from addressed sphere
vertices to singular one-currents. -/
def pointEndpointPathMorphism (labeling : StarPointLabeling) :
    SphereSingularChainComplex.X 0 ⟶ SphereSingularChainComplex.X 1 :=
  CategoryTheory.Limits.Sigma.desc fun simplex =>
    ModuleCat.ofHom
      { toFun := fun coefficient => coefficient •
          simplexGenerator
            (pointEndpointPath labeling (simplexVertexPoint simplex 0))
        map_add' := fun left right => add_smul left right _
        map_smul' := by
          intro scalar coefficient
          simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
          rfl }

@[simp]
theorem pointEndpointPathMorphism_simplexGenerator
    (labeling : StarPointLabeling) (simplex : SphereSingularSimplex 0) :
    pointEndpointPathMorphism labeling (simplexGenerator simplex) =
      simplexGenerator
        (pointEndpointPath labeling (simplexVertexPoint simplex 0)) := by
  change ((CategoryTheory.Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 0 => rationalCoefficient) simplex ≫
        CategoryTheory.Limits.Sigma.desc (fun source => ModuleCat.ofHom
          { toFun := fun coefficient : ℚ => coefficient •
              simplexGenerator
                (pointEndpointPath labeling (simplexVertexPoint source 0))
            map_add' := fun left right => add_smul left right _
            map_smul' := by
              intro scalar coefficient
              simp only [RingHom.id_apply, smul_eq_mul, mul_smul] })) (1 : ℚ)) = _
  rw [CategoryTheory.Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- [proved-derived; formal-checked] The actual point at a refined segment vertex is the source
point used by the global endpoint-path receiver. -/
theorem simplexVertexPoint_refinedEdge
    {chain : SphereChain 1} {scale : ℕ}
    (cell : RefinedEdgeCell chain scale) (index : Fin 2) :
    simplexVertexPoint (refinedEdgeSimplex cell) index =
      refinedEdgeSourceMap cell (stdSimplex.vertex index) := rfl

/-- [definition] The normalized carrier selected by a family.  It is written directly in the
`RefinedEdgeCell` chart so finite incidence and its `Fintype` remain available without a
projection-induced type shadow. -/
def selectedRefinedEdgeCarrier
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (cell : RefinedEdgeCell chain family.scale) : CommonStarEdge :=
  refinedEdgeCommonStarCarrier lebesgue family.labeling cell

/-- [proved-derived; formal-checked] Every local vertical edge-prism path is literally the
point-natural path of its actual endpoint. -/
theorem edgeHomotopyVertexSimplex_refinedEdge
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (cell : RefinedEdgeCell chain family.scale) (index : Fin 2) :
    edgeHomotopyVertexSimplex
        (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy index =
      pointEndpointPath
        (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
        (refinedEdgeSourceMap cell (stdSimplex.vertex index)) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  simp only [edgeHomotopyVertexSimplex, pointEndpointPath,
    Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  change (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy
      (segmentTime point, stdSimplex.vertex index) =
    (pointCommonStarEdge
        (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
        (refinedEdgeSourceMap cell (stdSimplex.vertex index))).affineSphereHomotopy
      (segmentTime point, stdSimplex.vertex 0)
  apply CommonStarEdge.affineSphereHomotopy_vertex_congr
  · rfl
  · simp only [selectedRefinedEdgeCarrier, refinedEdgeCommonStarCarrier,
      pointCommonStarEdge]
    exact refinedEdgeLabels_endpoint lebesgue family.labeling cell index

/-- [proved-derived; formal-checked] On one refined edge, the endpoint-path morphism of the
singular boundary is terminal path minus initial path. -/
theorem pointEndpointPathMorphism_boundary_refinedEdge
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (cell : RefinedEdgeCell chain family.scale) :
    pointEndpointPathMorphism
        (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
        (SphereSingularChainComplex.d 1 0
          (simplexGenerator (refinedEdgeSimplex cell))) =
      simplexGenerator
          (pointEndpointPath
            (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
            (refinedEdgeSourceMap cell (stdSimplex.vertex 1))) -
        simplexGenerator
          (pointEndpointPath
            (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
            (refinedEdgeSourceMap cell (stdSimplex.vertex 0))) := by
  have boundaryLaw :
      SphereSingularChainComplex.d 1 0
          (simplexGenerator (refinedEdgeSimplex cell)) =
        simplexGenerator (simplexFace 0 (refinedEdgeSimplex cell)) -
          simplexGenerator (simplexFace 1 (refinedEdgeSimplex cell)) := by
    rw [boundary_simplexGenerator, Fin.sum_univ_two]
    norm_num
    module
  rw [boundaryLaw, map_sub,
    pointEndpointPathMorphism_simplexGenerator,
    pointEndpointPathMorphism_simplexGenerator]
  rw [simplexVertexPoint_face, simplexVertexPoint_face]
  change simplexGenerator
        (pointEndpointPath
          (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
          (simplexVertexPoint (refinedEdgeSimplex cell) 1)) -
      simplexGenerator
        (pointEndpointPath
          (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
          (simplexVertexPoint (refinedEdgeSimplex cell) 0)) = _
  rw [simplexVertexPoint_refinedEdge, simplexVertexPoint_refinedEdge]

/-! ## The complete refined edge-prism current -/

/-- [definition] Weighted common-star prism over the complete refined edge population. -/
def refinedEdgePrismCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  ∑ cell : RefinedEdgeCell chain family.scale,
    refinedEdgeCoefficient cell •
      edgeHomotopyPrism (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy

/-- [definition] The exact refined source current under the selected family scale. -/
def refinedEdgeLowerCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) : SphereChain 1 :=
  ∑ cell : RefinedEdgeCell chain family.scale,
    refinedEdgeCoefficient cell • simplexGenerator (refinedEdgeSimplex cell)

/-- [definition] The ordered raw affine-label edge population at the upper prism boundary. -/
def refinedEdgeUpperCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) : SphereChain 1 :=
  ∑ cell : RefinedEdgeCell chain family.scale,
    refinedEdgeCoefficient cell •
      simplexGenerator
        (rawAffineLabelEdge (refinedEdgeLabels lebesgue family.labeling cell))

/-- [definition] The retained initial-minus-terminal vertical endpoint-path current. -/
def refinedEdgeVerticalCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) : SphereChain 1 :=
  ∑ cell : RefinedEdgeCell chain family.scale,
    refinedEdgeCoefficient cell •
      (simplexGenerator
          (edgeHomotopyVertexSimplex
            (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy 0) -
        simplexGenerator
          (edgeHomotopyVertexSimplex
            (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy 1))

/-- [proved-derived; formal-checked] The horizontal lower edge of each local prism is the exact
refined singular source edge. -/
theorem edgeHomotopyEndSimplex_refinedEdge_zero
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (cell : RefinedEdgeCell chain family.scale) :
    edgeHomotopyEndSimplex
        (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy 0 =
      refinedEdgeSimplex cell := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  simp only [edgeHomotopyEndSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  change (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy (0, point) =
    refinedEdgeSourceMap cell point
  exact CommonStarEdge.affineSphereHomotopy_zero _ point

/-- [proved-derived; formal-checked] The horizontal upper edge is the raw affine realization of
the complete ordered endpoint-label word. -/
theorem edgeHomotopyEndSimplex_refinedEdge_one
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (cell : RefinedEdgeCell chain family.scale) :
    edgeHomotopyEndSimplex
        (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy 1 =
      rawAffineLabelEdge (refinedEdgeLabels lebesgue family.labeling cell) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  simp only [edgeHomotopyEndSimplex, rawAffineLabelEdge,
    Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  change (selectedRefinedEdgeCarrier family cell).affineSphereHomotopy (1, point) =
    lowLabelSphereMap 1 (by omega)
      (refinedEdgeLabels lebesgue family.labeling cell) point
  exact CommonStarEdge.affineSphereHomotopy_one _ point

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The complete prism boundary is upper minus lower plus the
retained vertical endpoint current. -/
theorem boundary_refinedEdgePrismCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) :
    SphereSingularChainComplex.d 2 1 (refinedEdgePrismCurrent family) =
      refinedEdgeUpperCurrent family - refinedEdgeLowerCurrent family +
        refinedEdgeVerticalCurrent family := by
  classical
  rw [refinedEdgePrismCurrent, map_sum]
  simp only [map_smul, boundary_edgeHomotopyPrism,
    edgeHomotopyEndSimplex_refinedEdge_one,
    edgeHomotopyEndSimplex_refinedEdge_zero]
  rw [refinedEdgeUpperCurrent, refinedEdgeLowerCurrent,
    refinedEdgeVerticalCurrent]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro cell _
  module

/-- [proved-derived; formal-checked] The complete vertical prism population factors through the
actual refined singular boundary.  This is the exact local-to-global seam descent. -/
theorem refinedEdgeVerticalCurrent_eq_neg_endpointPath_boundary
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) :
    refinedEdgeVerticalCurrent family =
      -pointEndpointPathMorphism
        (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
        (SphereSingularChainComplex.d 1 0 (refinedEdgeLowerCurrent family)) := by
  classical
  rw [refinedEdgeVerticalCurrent, refinedEdgeLowerCurrent, map_sum]
  simp only [map_smul]
  rw [map_sum]
  simp only [map_smul, pointEndpointPathMorphism_boundary_refinedEdge,
    edgeHomotopyVertexSimplex_refinedEdge]
  simp_rw [smul_sub, Finset.sum_sub_distrib]
  module

/-- [proved-derived; formal-checked] A closed source current has no residual vertical endpoint
current after any uniformly selected refinement. -/
theorem refinedEdgeVerticalCurrent_eq_zero_of_cycle
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (closed : SphereSingularChainComplex.d 1 0 chain = 0) :
    refinedEdgeVerticalCurrent family = 0 := by
  rw [refinedEdgeVerticalCurrent_eq_neg_endpointPath_boundary]
  have lowerLaw : refinedEdgeLowerCurrent family =
      iteratedBarycentricEdgeSubdivision family.scale chain :=
    sum_refinedEdgeCoefficient_simplexGenerator chain family.scale
  rw [lowerLaw, boundary_iteratedBarycentricEdgeSubdivision, closed, map_zero, neg_zero]

/-! ## Exact normalization and finite tetrahedral filling -/

/-- [definition] The retained fold/constant correction for every ordered raw label edge. -/
def refinedEdgeCorrectionCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  ∑ cell : RefinedEdgeCell chain family.scale,
    refinedEdgeCoefficient cell •
      rawAffineLabelEdgeCorrection
        (refinedEdgeLabels lebesgue family.labeling cell 0)
        (refinedEdgeLabels lebesgue family.labeling cell 1)

/-- [definition] The finite tetrahedral edge current carried by the complete refined source. -/
def refinedEdgeFiniteCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) :
    tetrahedralChainComplex.X 1 :=
  pointCarryMorphism
    (refinedEdgeClosedStarPointLabeling lebesgue family.labeling) 1
    (refinedEdgeLowerCurrent family)

/-- [proved-derived; formal-checked] The correction boundary is the raw upper current minus the
sphere realization of its exact finite point-carry current. -/
theorem boundary_refinedEdgeCorrectionCurrent
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) :
    SphereSingularChainComplex.d 2 1 (refinedEdgeCorrectionCurrent family) =
      refinedEdgeUpperCurrent family -
        edgeRealization (refinedEdgeFiniteCurrent family) := by
  classical
  rw [refinedEdgeCorrectionCurrent, map_sum]
  simp only [map_smul, rawAffineLabelEdgeCorrection_boundary]
  rw [refinedEdgeUpperCurrent, refinedEdgeFiniteCurrent,
    refinedEdgeLowerCurrent, map_sum]
  simp only [map_smul, refinedEdgeLabels_eq_simplexPointLabels]
  rw [map_sum]
  simp only [map_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro cell _
  have labelPairLaw :
      ![simplexPointLabels
          (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
          (refinedEdgeSimplex cell) 0,
        simplexPointLabels
          (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
          (refinedEdgeSimplex cell) 1] =
        simplexPointLabels
          (refinedEdgeClosedStarPointLabeling lebesgue family.labeling)
          (refinedEdgeSimplex cell) := by
    funext index
    fin_cases index <;> rfl
  rw [labelPairLaw, pointCarryMorphism_simplexGenerator]
  simp only [pointCarry]
  module

/-- [proved-derived; formal-checked] A closed refined sphere current carries to a closed finite
tetrahedral edge current. -/
theorem vertexBoundary_refinedEdgeFiniteCurrent_eq_zero_of_cycle
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (closed : SphereSingularChainComplex.d 1 0 chain = 0) :
    vertexBoundary (refinedEdgeFiniteCurrent family) = 0 := by
  rw [refinedEdgeFiniteCurrent, ← pointCarryMorphism_boundary_one]
  have lowerLaw : refinedEdgeLowerCurrent family =
      iteratedBarycentricEdgeSubdivision family.scale chain :=
    sum_refinedEdgeCoefficient_simplexGenerator chain family.scale
  rw [lowerLaw, boundary_iteratedBarycentricEdgeSubdivision, closed, map_zero]

/-- [definition] Explicit finite face filling transported back to the singular sphere complex. -/
def refinedEdgeFiniteFilling
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  faceRealization (edgeCycleFiller (refinedEdgeFiniteCurrent family))

/-- [proved-derived; formal-checked] For a closed source, the finite filling returns exactly the
realized finite edge current. -/
theorem boundary_refinedEdgeFiniteFilling_of_cycle
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (closed : SphereSingularChainComplex.d 1 0 chain = 0) :
    SphereSingularChainComplex.d 2 1 (refinedEdgeFiniteFilling family) =
      edgeRealization (refinedEdgeFiniteCurrent family) := by
  rw [refinedEdgeFiniteFilling, faceRealization_boundary,
    faceBoundary_edgeCycleFiller _
      (vertexBoundary_refinedEdgeFiniteCurrent_eq_zero_of_cycle family closed)]

/-! ## The returned singular filling -/

/-- [definition] The exact degree-one filling current: finite fill, minus affine prism, plus
ordered-edge normalization, minus accumulated refinement prism. -/
def sphereDegreeOneFiller
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  refinedEdgeFiniteFilling family - refinedEdgePrismCurrent family +
      refinedEdgeCorrectionCurrent family -
    iteratedEdgeSubdivisionHomotopy family.scale chain

/-- [proved-derived; formal-checked] Every selected carrier family returns an explicit singular
two-current whose boundary is its closed source one-current. -/
theorem boundary_sphereDegreeOneFiller
    {chain : SphereChain 1} {lebesgue : StarLebesgueLabel}
    (family : RefinedEdgeAffineCarrierFamily chain lebesgue)
    (closed : SphereSingularChainComplex.d 1 0 chain = 0) :
    SphereSingularChainComplex.d 2 1 (sphereDegreeOneFiller family) = chain := by
  rw [sphereDegreeOneFiller]
  simp only [map_sub, map_add]
  rw [boundary_refinedEdgeFiniteFilling_of_cycle family closed,
    boundary_refinedEdgePrismCurrent,
    refinedEdgeVerticalCurrent_eq_zero_of_cycle family closed,
    boundary_refinedEdgeCorrectionCurrent,
    boundary_iteratedEdgeSubdivisionHomotopy]
  have lowerLaw : refinedEdgeLowerCurrent family =
      iteratedBarycentricEdgeSubdivision family.scale chain :=
    sum_refinedEdgeCoefficient_simplexGenerator chain family.scale
  rw [lowerLaw]
  module

/-- [proved-derived; formal-checked] Every rational singular one-cycle on the modeled two-sphere
is the boundary of a constructed rational singular two-chain. -/
theorem exists_sphereDegreeOneFilling
    (chain : SphereChain 1)
    (closed : SphereSingularChainComplex.d 1 0 chain = 0) :
    ∃ filling : SphereChain 2,
      SphereSingularChainComplex.d 2 1 filling = chain := by
  obtain ⟨lebesgue⟩ := exists_starLebesgueLabel
  obtain ⟨family⟩ := nonempty_refinedEdgeAffineCarrierFamily chain lebesgue
  exact ⟨sphereDegreeOneFiller family,
    boundary_sphereDegreeOneFiller family closed⟩

section Audit

#print axioms boundary_iteratedEdgeSubdivisionHomotopy
#print axioms sum_refinedEdgeCoefficient_simplexGenerator
#print axioms pointEndpointPathMorphism_simplexGenerator
#print axioms edgeHomotopyVertexSimplex_refinedEdge
#print axioms pointEndpointPathMorphism_boundary_refinedEdge
#print axioms boundary_refinedEdgePrismCurrent
#print axioms refinedEdgeVerticalCurrent_eq_neg_endpointPath_boundary
#print axioms refinedEdgeVerticalCurrent_eq_zero_of_cycle
#print axioms boundary_refinedEdgeCorrectionCurrent
#print axioms vertexBoundary_refinedEdgeFiniteCurrent_eq_zero_of_cycle
#print axioms boundary_refinedEdgeFiniteFilling_of_cycle
#print axioms boundary_sphereDegreeOneFiller
#print axioms exists_sphereDegreeOneFilling

end Audit

end Soma.Holonics.Millennium.HodgeSphereDegreeOneFilling
