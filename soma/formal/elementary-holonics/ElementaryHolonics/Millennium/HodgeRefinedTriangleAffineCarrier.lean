import ElementaryHolonics.Millennium.HodgeCommonStarAffineCarrier
import ElementaryHolonics.Millennium.HodgeRefinedTriangleClosedStar

/-!
# Uniform common-star affine carriers on an actual refined two-chain

`HodgeRefinedTriangleClosedStar` constructs one fixed refinement depth and one coherent
closed-star label on the complete finite vertex population of an arbitrary singular two-chain.
`HodgeCommonStarAffineCarrier` constructs the exact boundary homotopy once one triangle and its
three carried labels have been supplied.  This file closes the incidence joint between those two
owners.

The source of each carrier is the actual refined singular triangle, not a copied local simplex.
Its labels are read at the three nonduplicated vertices of the standing degenerate tetrahedral
presentation.  Closed-star incidence then carries the complete triangle image in every selected
star.  One scale and one labeling therefore produce a face-addressed affine homotopy for every
supported refined cell simultaneously.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the existing fixed-scale refinement, coherent
closed-star labeling, and exact common-star affine homotopy.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRefinedTriangleAffineCarrier

open CategoryTheory Set Topology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeRefinedTriangleClosedStar
open Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier
open Soma.Holonics.Millennium.HodgePointCarry

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- [definition] The actual continuous realization of one addressed refined triangle cell. -/
def refinedTriangleSourceMap {chain : SphereChain 2} {scale : ℕ}
    (cell : RefinedTriangleCell chain scale) :
    C(Triangle, HodgeTwoSphereFundamentalCycle.TwoSphere) :=
  TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2)) (refinedTriangleSimplex cell)

/-- [proved-derived; formal-checked] The standing tetrahedral codegeneracy has the original
triangle as its face opposite vertex zero. -/
theorem tetrahedronToTriangle_comp_face_zero :
    tetrahedronToTriangle.comp (simplexFaceMap (degree := 2) 0) =
      ContinuousMap.id Triangle := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map
      (SimplexCategory.σ (0 : Fin 3)).toOrderHom
        (stdSimplex.map
          (SimplexCategory.δ (0 : Fin 4)).toOrderHom point) = point
  rw [stdSimplex.map_comp_apply]
  change stdSimplex.map
      ((SimplexCategory.δ (Fin.castSucc (0 : Fin 3)) ≫
        SimplexCategory.σ (0 : Fin 3)).toOrderHom) point = point
  rw [SimplexCategory.δ_comp_σ_self]
  simpa using (stdSimplex.map_id_apply point)

/-- [proved-derived; formal-checked] Restricting the degenerate tetrahedral occurrence to its
nonduplicated face returns the exact refined singular triangle realization. -/
theorem refinedTriangleRealization_comp_face_zero
    {chain : SphereChain 2} {scale : ℕ}
    (cell : RefinedTriangleCell chain scale) :
    (refinedTriangleRealization cell).comp (simplexFaceMap (degree := 2) 0) =
      refinedTriangleSourceMap cell := by
  change ((refinedTriangleSourceMap cell).comp tetrahedronToTriangle).comp
      (simplexFaceMap (degree := 2) 0) = refinedTriangleSourceMap cell
  rw [ContinuousMap.comp_assoc, tetrahedronToTriangle_comp_face_zero]
  exact ContinuousMap.comp_id _

/-- [definition] The three coherent labels at the nonduplicated triangle vertices. -/
def refinedCellLabels {chain : SphereChain 2} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (cell : RefinedTriangleCell chain scale) :
    Fin 3 → HodgeTetrahedralChainComplex.TetraVertex :=
  fun index =>
    (refinedClosedStarPointLabeling lebesgue labeling).label
      ((refinedTriangleComplex chain scale).point
        ((refinedTriangleComplex chain scale).cellVertex cell index.succ))

/-- [proved-derived; formal-checked] The standing codegeneracy sends each nonduplicated
tetrahedral vertex to the correspondingly addressed triangle vertex. -/
theorem tetrahedronToTriangle_vertex_succ (index : Fin 3) :
    tetrahedronToTriangle (stdSimplex.vertex index.succ) =
      stdSimplex.vertex index := by
  change stdSimplex.map (SimplexCategory.σ (0 : Fin 3)).toOrderHom
      (stdSimplex.vertex index.succ) = stdSimplex.vertex index
  rw [stdSimplex.map_vertex]
  congr 1

/-- [proved-derived; formal-checked] The actual sphere point at a nonduplicated tetrahedral
occurrence is the corresponding vertex of the refined source triangle. -/
theorem refinedTriangleRealization_vertex_succ
    {chain : SphereChain 2} {scale : ℕ}
    (cell : RefinedTriangleCell chain scale) (index : Fin 3) :
    refinedTriangleRealization cell (stdSimplex.vertex index.succ) =
      refinedTriangleSourceMap cell (stdSimplex.vertex index) := by
  change refinedTriangleSourceMap cell
      (tetrahedronToTriangle (stdSimplex.vertex index.succ)) = _
  rw [tetrahedronToTriangle_vertex_succ]

/-- [proved-derived; formal-checked] A refined cell label is determined only by its actual
addressed sphere vertex, rather than by the parent-cell copy in which that vertex occurs. -/
theorem refinedCellLabels_vertex
    {chain : SphereChain 2} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (cell : RefinedTriangleCell chain scale) (index : Fin 3) :
    refinedCellLabels lebesgue labeling cell index =
      (refinedClosedStarPointLabeling lebesgue labeling).label
        (refinedTriangleSourceMap cell (stdSimplex.vertex index)) := by
  change (refinedClosedStarPointLabeling lebesgue labeling).label
      (refinedTriangleRealization cell (stdSimplex.vertex index.succ)) = _
  rw [refinedTriangleRealization_vertex_succ]

/-- [proved-derived; formal-checked] The carrier's ordered labels are exactly the point-natural
labels of the addressed refined source triangle.  This is the normalization seam between the
degenerate tetrahedral presentation and the genuine degree-two source occurrence. -/
theorem refinedCellLabels_eq_simplexPointLabels
    {chain : SphereChain 2} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (cell : RefinedTriangleCell chain scale) :
    refinedCellLabels lebesgue labeling cell =
      simplexPointLabels
        (refinedClosedStarPointLabeling lebesgue labeling)
        (refinedTriangleSimplex cell) := by
  funext index
  rw [refinedCellLabels_vertex]
  rfl

/-- [proved-derived; formal-checked] Equality of two actual addressed source edges forces equality
of their ordered global endpoint-label words.  This is the incidence seam needed by the prism
cancellation; no local-cell label choice remains. -/
theorem refinedCellLabels_face_congr
    {chain : SphereChain 2} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (first second : RefinedTriangleCell chain scale)
    (firstFace secondFace : Fin 3)
    (sourceLaw :
      (refinedTriangleSourceMap first).comp
          (simplexFaceMap (degree := 1) firstFace) =
        (refinedTriangleSourceMap second).comp
          (simplexFaceMap (degree := 1) secondFace)) :
    refinedCellLabels lebesgue labeling first ∘ firstFace.succAbove =
      refinedCellLabels lebesgue labeling second ∘ secondFace.succAbove := by
  funext index
  simp only [Function.comp_apply]
  rw [refinedCellLabels_vertex, refinedCellLabels_vertex]
  apply congrArg (refinedClosedStarPointLabeling lebesgue labeling).label
  have pointLaw := ContinuousMap.congr_fun sourceLaw (stdSimplex.vertex index)
  simp only [ContinuousMap.comp_apply, simplexFaceMap_vertex] at pointLaw
  exact pointLaw

/-- [proved-derived; formal-checked] Every point of the actual refined triangle lies in each of
the three coherently selected open stars. -/
theorem refinedTriangleSourceMap_carried
    {chain : SphereChain 2} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (cell : RefinedTriangleCell chain scale)
    (point : Triangle) (index : Fin 3) :
    refinedTriangleSourceMap cell point ∈
      vertexStar (refinedCellLabels lebesgue labeling cell index) := by
  apply refinedTriangleCell_range_carried lebesgue labeling cell index.succ
  refine ⟨simplexFaceMap (degree := 2) 0 point, ?_⟩
  exact ContinuousMap.congr_fun (refinedTriangleRealization_comp_face_zero cell) point

/-- [definition] The common-star affine carrier attached to one actual refined triangle cell. -/
def refinedTriangleCommonStarCarrier
    {chain : SphereChain 2} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (cell : RefinedTriangleCell chain scale) : CommonStarTriangle where
  source := refinedTriangleSourceMap cell
  labels := refinedCellLabels lebesgue labeling cell
  carried := refinedTriangleSourceMap_carried lebesgue labeling cell

/-- [definition] One fixed scale, one coherent closed-star labeling, and the resulting carrier on
every addressed cell of the refined source chain. -/
structure RefinedAffineCarrierFamily (chain : SphereChain 2)
    (lebesgue : StarLebesgueLabel) where
  scale : ℕ
  labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling
  carrier : (refinedTriangleComplex chain scale).Cell → CommonStarTriangle
  carrier_eq : carrier = refinedTriangleCommonStarCarrier lebesgue labeling

/-- [proved-derived; formal-checked] Every actual singular two-chain admits one uniform refined
family of exact common-star affine carriers. -/
theorem nonempty_refinedAffineCarrierFamily
    (chain : SphereChain 2) (lebesgue : StarLebesgueLabel) :
    Nonempty (RefinedAffineCarrierFamily chain lebesgue) := by
  obtain ⟨scale, ⟨labeling⟩⟩ :=
    exists_scale_refinedTriangleClosedStarLabeling chain lebesgue
  exact ⟨{
    scale := scale
    labeling := labeling
    carrier := refinedTriangleCommonStarCarrier lebesgue labeling
    carrier_eq := rfl }⟩

/-- [proved-derived; formal-checked] Every member of the uniform family starts at the exact
refined source occurrence. -/
theorem RefinedAffineCarrierFamily.homotopy_zero
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cell : (refinedTriangleComplex chain family.scale).Cell)
    (point : Triangle) :
    (family.carrier cell).affineSphereHomotopy (0, point) =
      refinedTriangleSourceMap cell point := by
  rw [family.carrier_eq]
  exact CommonStarTriangle.affineSphereHomotopy_zero _ _

/-- [proved-derived; formal-checked] Every member ends at the face-natural affine label
realization, with the same coherent global vertex labeling. -/
theorem RefinedAffineCarrierFamily.homotopy_one
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cell : (refinedTriangleComplex chain family.scale).Cell)
    (point : Triangle) :
    (family.carrier cell).affineSphereHomotopy (1, point) =
      lowLabelSphereMap 2 (by omega)
        (refinedCellLabels lebesgue family.labeling cell) point := by
  rw [family.carrier_eq]
  exact CommonStarTriangle.affineSphereHomotopy_one _ _

/-- [proved-derived; formal-checked] The uniform carrier family assigns the same complete edge
homotopy to any two cell faces which are the same addressed singular edge. -/
theorem RefinedAffineCarrierFamily.homotopy_face_congr
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (first second : (refinedTriangleComplex chain family.scale).Cell)
    (firstFace secondFace : Fin 3)
    (sourceLaw :
      (refinedTriangleSourceMap first).comp
          (simplexFaceMap (degree := 1) firstFace) =
        (refinedTriangleSourceMap second).comp
          (simplexFaceMap (degree := 1) secondFace)) :
    (family.carrier first).affineSphereHomotopy.comp
        (CommonStarTriangle.triangleCylinderFace firstFace) =
      (family.carrier second).affineSphereHomotopy.comp
        (CommonStarTriangle.triangleCylinderFace secondFace) := by
  rw [family.carrier_eq]
  apply CommonStarTriangle.affineSphereHomotopy_face_congr
  · exact sourceLaw
  · exact refinedCellLabels_face_congr lebesgue family.labeling
      first second firstFace secondFace sourceLaw

section Audit

#print axioms tetrahedronToTriangle_comp_face_zero
#print axioms refinedTriangleRealization_comp_face_zero
#print axioms refinedCellLabels_face_congr
#print axioms refinedCellLabels_eq_simplexPointLabels
#print axioms refinedTriangleSourceMap_carried
#print axioms nonempty_refinedAffineCarrierFamily
#print axioms RefinedAffineCarrierFamily.homotopy_zero
#print axioms RefinedAffineCarrierFamily.homotopy_one
#print axioms RefinedAffineCarrierFamily.homotopy_face_congr

end Audit

end Soma.Holonics.Millennium.HodgeRefinedTriangleAffineCarrier
