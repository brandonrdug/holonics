import HolonicsResearch.Hodge.HodgeAffineTriangleBoundarySource
import HolonicsResearch.Hodge.HodgeBarycentricTetrahedron

/-!
# The triangle source is received and its affine sampling defect remains explicit.

This is one source owner of the canonical affine complex. Existing declarations
keep their namespace; the canonical entry imports the complete source family.
-/

noncomputable section

namespace Holonics.Hodge.HodgeBarycentricAffineSourceComplex

open Holonics.Hodge.HodgeProjectiveLineSingularReduction
open Holonics.Hodge.HodgeTwoSphereFundamentalCycle
open Holonics.Hodge.HodgeStellarSubdivision
open Holonics.Hodge.HodgeStellarSubdivisionHomotopy
open Holonics.Hodge.HodgeBarycentricEdgeSubdivision
open Holonics.Hodge.HodgeBarycentricTriangleSubdivision
open Holonics.Hodge.HodgeBarycentricSubdivisionHomotopy
open Holonics.Hodge.HodgeBarycentricDegreeTwoFilling

open CategoryTheory

/-! ## Common-apex realization of the closed source current -/

/-- Reparameterize one parent sphere simplex by an addressed triangle source map. -/
def reparameterizedTriangle (base : C(Triangle, Triangle))
    (simplex : SphereSingularSimplex 2) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2)) simplex).comp base)

/-- The fixed-apex affine cone on one addressed source edge. -/
def commonApexEdgeVertices (edge : C(Segment, Triangle)) : Fin 3 → Triangle :=
  Fin.cases triangleBarycenter fun vertex : Fin 2 => edge (stdSimplex.vertex vertex)

def commonApexEdgeMap (edge : C(Segment, Triangle)) : C(Triangle, Triangle) :=
  triangleAffineMap (commonApexEdgeVertices edge)

def commonApexEdgeSubsimplex (edge : C(Segment, Triangle))
    (simplex : SphereSingularSimplex 2) : SphereSingularSimplex 2 :=
  reparameterizedTriangle (commonApexEdgeMap edge) simplex

/-- Source-map realization into the degree-two singular current of the parent simplex. -/
def sourceTriangleRealization (simplex : SphereSingularSimplex 2) :
    SourceTriangleChain →ₗ[ℚ] SphereSingularChainComplex.X 2 :=
  Finsupp.linearCombination ℚ fun base =>
    simplexGenerator (reparameterizedTriangle base simplex)

/-- Source-edge cone realization with the parent simplex's barycentre as common apex. -/
def sourceEdgeConeRealization (simplex : SphereSingularSimplex 2) :
    SourceEdgeChain →ₗ[ℚ] SphereSingularChainComplex.X 2 :=
  Finsupp.linearCombination ℚ fun edge =>
    simplexGenerator (commonApexEdgeSubsimplex edge simplex)

/-- Source-triangle cone realization into degree three. -/
def sourceTriangleConeRealization (simplex : SphereSingularSimplex 2) :
    SourceTriangleChain →ₗ[ℚ] SphereSingularChainComplex.X 3 :=
  Finsupp.linearCombination ℚ fun base =>
    simplexGenerator (conedTriangleSubsimplex base simplex)

@[simp]
theorem sourceTriangleRealization_single (simplex : SphereSingularSimplex 2)
    (base : C(Triangle, Triangle)) (coefficient : ℚ) :
    sourceTriangleRealization simplex (Finsupp.single base coefficient) =
      coefficient • simplexGenerator (reparameterizedTriangle base simplex) := by
  simp [sourceTriangleRealization]

@[simp]
theorem sourceEdgeConeRealization_single (simplex : SphereSingularSimplex 2)
    (edge : C(Segment, Triangle)) (coefficient : ℚ) :
    sourceEdgeConeRealization simplex (Finsupp.single edge coefficient) =
      coefficient • simplexGenerator (commonApexEdgeSubsimplex edge simplex) := by
  simp [sourceEdgeConeRealization]

@[simp]
theorem sourceTriangleConeRealization_single (simplex : SphereSingularSimplex 2)
    (base : C(Triangle, Triangle)) (coefficient : ℚ) :
    sourceTriangleConeRealization simplex (Finsupp.single base coefficient) =
      coefficient • simplexGenerator (conedTriangleSubsimplex base simplex) := by
  simp [sourceTriangleConeRealization]

theorem coneOverTriangleFaceMap_eq_commonApexEdgeMap
    (base : C(Triangle, Triangle)) (omitted : Fin 3) :
    coneOverTriangleFaceMap base omitted =
      commonApexEdgeMap (base.comp (simplexFaceMap (degree := 1) omitted)) := by
  rfl

theorem conedTriangleSubsimplex_face_succ_commonApex
    (base : C(Triangle, Triangle)) (omitted : Fin 3)
    (simplex : SphereSingularSimplex 2) :
    simplexFace omitted.succ (conedTriangleSubsimplex base simplex) =
      commonApexEdgeSubsimplex
        (base.comp (simplexFaceMap (degree := 1) omitted)) simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [conedTriangleSubsimplex, commonApexEdgeSubsimplex,
    reparameterizedTriangle, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, coneOverTriangleMap_face_succ,
    coneOverTriangleFaceMap_eq_commonApexEdgeMap]

theorem conedTriangleSubsimplex_face_zero_affine
    (vertices : Fin 3 → Triangle) (simplex : SphereSingularSimplex 2) :
    simplexFace 0
        (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
      reparameterizedTriangle (triangleAffineMap vertices) simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [conedTriangleSubsimplex, reparameterizedTriangle,
    Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, coneOverTriangleMap_face_zero_affine]

/-- Boundary of one affine common-apex cone: its exterior base minus the common-apex realization
of its complete source boundary. -/
theorem boundary_sourceTriangleConeRealization_single_affine
    (vertices : Fin 3 → Triangle) (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (triangleAffineMap vertices))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (triangleAffineMap vertices)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (triangleAffineMap vertices))) := by
  classical
  have hfaceOne :
      simplexFace 1
          (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
        commonApexEdgeSubsimplex
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 0)) simplex := by
    simpa using conedTriangleSubsimplex_face_succ_commonApex
      (triangleAffineMap vertices) 0 simplex
  have hfaceTwo :
      simplexFace 2
          (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
        commonApexEdgeSubsimplex
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 1)) simplex := by
    simpa using conedTriangleSubsimplex_face_succ_commonApex
      (triangleAffineMap vertices) 1 simplex
  have hfaceThree :
      simplexFace 3
          (conedTriangleSubsimplex (triangleAffineMap vertices) simplex) =
        commonApexEdgeSubsimplex
          ((triangleAffineMap vertices).comp (simplexFaceMap (degree := 1) 2)) simplex := by
    simpa using conedTriangleSubsimplex_face_succ_commonApex
      (triangleAffineMap vertices) 2 simplex
  simp only [sourceTriangleGenerator, sourceTriangleConeRealization_single,
    sourceTriangleRealization_single, sourceBoundary_single,
    sourceTriangleBoundary, one_smul,
    boundary_simplexGenerator]
  rw [Fin.sum_univ_four]
  repeat rw [Fin.sum_univ_three]
  rw [conedTriangleSubsimplex_face_zero_affine, hfaceOne, hfaceTwo, hfaceThree]
  simp only [map_add, map_smul, sourceEdgeGenerator,
    sourceEdgeConeRealization_single, one_smul]
  norm_num
  module

/-- The identity source triangle is affine with its three canonical vertices. -/
theorem triangleAffineMap_canonicalVertices :
    triangleAffineMap (fun vertex : Fin 3 => stdSimplex.vertex vertex) =
      ContinuousMap.id Triangle := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  fin_cases coordinate <;>
    simp [triangleAffineMap_apply, Fin.sum_univ_three]

/-- Every lifted edge-prism base is affine.  The returned vertex chart is exact, so the common
apex cone retains the entire base rather than merely its three samples. -/
theorem residualPrismBase_eq_triangleAffineMap_vertices
    (outerFace : Fin 3) (kind : Fin 3) :
    residualPrismBase outerFace kind =
      triangleAffineMap (fun vertex =>
        residualPrismBase outerFace kind (stdSimplex.vertex vertex)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  fin_cases outerFace <;> fin_cases kind <;> fin_cases coordinate <;>
    simp [residualPrismBase, edgeHomotopyMainMap, edgeHomotopyFoldMap,
      edgeHomotopyConstantMap, triangleToSegmentAffineMap_apply,
      triangleAffineMap_apply, Fin.sum_univ_three]

theorem boundary_sourceTriangleConeRealization_barycentric
    (outerFace : Fin 3) (half : Fin 2) (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (barycentricTriangleMap outerFace half))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (barycentricTriangleMap outerFace half)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (barycentricTriangleMap outerFace half))) := by
  exact boundary_sourceTriangleConeRealization_single_affine
    (barycentricTriangleVertices outerFace half) simplex

theorem boundary_sourceTriangleConeRealization_id
    (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (ContinuousMap.id Triangle))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (ContinuousMap.id Triangle)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (ContinuousMap.id Triangle))) := by
  simpa only [triangleAffineMap_canonicalVertices] using
    boundary_sourceTriangleConeRealization_single_affine
      (fun vertex : Fin 3 => stdSimplex.vertex vertex) simplex

theorem boundary_sourceTriangleConeRealization_prism
    (outerFace : Fin 3) (kind : Fin 3) (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex
          (sourceTriangleGenerator (residualPrismBase outerFace kind))) =
      sourceTriangleRealization simplex
          (sourceTriangleGenerator (residualPrismBase outerFace kind)) -
        sourceEdgeConeRealization simplex
          (sourceBoundary
            (sourceTriangleGenerator (residualPrismBase outerFace kind))) := by
  rw [residualPrismBase_eq_triangleAffineMap_vertices]
  exact boundary_sourceTriangleConeRealization_single_affine _ simplex

/-- The common-apex cone fills the universal source residual up to the cone of its source
boundary.  This is the exact chain-contraction identity before closedness is consumed. -/
theorem boundary_sourceTriangleConeRealization_sourceBarycentricResidual
    (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex sourceBarycentricResidual) =
      sourceTriangleRealization simplex sourceBarycentricResidual -
        sourceEdgeConeRealization simplex
          (sourceBoundary sourceBarycentricResidual) := by
  classical
  rw [sourceBarycentricResidual]
  simp only [map_sub, map_sum, map_smul]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  rw [boundary_sourceTriangleConeRealization_barycentric 0 0,
    boundary_sourceTriangleConeRealization_barycentric 0 1,
    boundary_sourceTriangleConeRealization_barycentric 1 0,
    boundary_sourceTriangleConeRealization_barycentric 1 1,
    boundary_sourceTriangleConeRealization_barycentric 2 0,
    boundary_sourceTriangleConeRealization_barycentric 2 1,
    boundary_sourceTriangleConeRealization_id,
    boundary_sourceTriangleConeRealization_prism 0 0,
    boundary_sourceTriangleConeRealization_prism 0 1,
    boundary_sourceTriangleConeRealization_prism 0 2,
    boundary_sourceTriangleConeRealization_prism 1 0,
    boundary_sourceTriangleConeRealization_prism 1 1,
    boundary_sourceTriangleConeRealization_prism 1 2,
    boundary_sourceTriangleConeRealization_prism 2 0,
    boundary_sourceTriangleConeRealization_prism 2 1,
    boundary_sourceTriangleConeRealization_prism 2 2]
  module

/-- Closedness removes the entire side-face population, so the common-apex cone returns the
sixteen-term source residual exactly. -/
theorem boundary_sourceTriangleConeRealization_sourceBarycentricResidual_eq_realization
    (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2
        (sourceTriangleConeRealization simplex sourceBarycentricResidual) =
      sourceTriangleRealization simplex sourceBarycentricResidual := by
  rw [boundary_sourceTriangleConeRealization_sourceBarycentricResidual,
    sourceBoundary_sourceBarycentricResidual, map_zero, sub_zero]

theorem reparameterizedTriangle_barycentric (outerFace : Fin 3) (half : Fin 2)
    (simplex : SphereSingularSimplex 2) :
    reparameterizedTriangle (barycentricTriangleMap outerFace half) simplex =
      barycentricTriangleSubsimplex outerFace half simplex := rfl

theorem reparameterizedTriangle_id (simplex : SphereSingularSimplex 2) :
    reparameterizedTriangle (ContinuousMap.id Triangle) simplex = simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  simp [reparameterizedTriangle]

/-- The three prism kinds, after lifting into one outer face of the parent triangle, reconstruct
the exact degree-one homotopy triangles already used by `P₁∂`. -/
theorem reparameterizedTriangle_residualPrismBase
    (outerFace : Fin 3) (kind : Fin 3) (simplex : SphereSingularSimplex 2) :
    reparameterizedTriangle (residualPrismBase outerFace kind) simplex =
      edgeHomotopyTriangle
        (match kind with
        | 0 => edgeHomotopyMainMap
        | 1 => edgeHomotopyFoldMap
        | _ => edgeHomotopyConstantMap)
        (simplexFace outerFace simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  simp only [reparameterizedTriangle, residualPrismBase, edgeHomotopyTriangle,
    Equiv.apply_symm_apply]
  rw [simplexFace_realization, ContinuousMap.comp_assoc]
  rfl

/-- The universal affine source current realizes to the exact recursive degree-two defect on each
addressed sphere simplex. -/
theorem sourceTriangleRealization_sourceBarycentricResidual
    (simplex : SphereSingularSimplex 2) :
    sourceTriangleRealization simplex sourceBarycentricResidual =
      barycentricTriangleHomotopyDefectMorphism (simplexGenerator simplex) := by
  classical
  rw [sourceBarycentricResidual]
  simp only [map_sub, map_sum, map_smul, sourceTriangleGenerator,
    sourceTriangleRealization_single, one_smul]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  rw [reparameterizedTriangle_barycentric 0 0,
    reparameterizedTriangle_barycentric 0 1,
    reparameterizedTriangle_barycentric 1 0,
    reparameterizedTriangle_barycentric 1 1,
    reparameterizedTriangle_barycentric 2 0,
    reparameterizedTriangle_barycentric 2 1,
    reparameterizedTriangle_id,
    reparameterizedTriangle_residualPrismBase 0 0,
    reparameterizedTriangle_residualPrismBase 0 1,
    reparameterizedTriangle_residualPrismBase 0 2,
    reparameterizedTriangle_residualPrismBase 1 0,
    reparameterizedTriangle_residualPrismBase 1 1,
    reparameterizedTriangle_residualPrismBase 1 2,
    reparameterizedTriangle_residualPrismBase 2 0,
    reparameterizedTriangle_residualPrismBase 2 1,
    reparameterizedTriangle_residualPrismBase 2 2]
  rw [barycentricTriangleHomotopyDefectMorphism]
  change _ =
    barycentricTriangleSubdivisionMorphism (simplexGenerator simplex) -
      simplexGenerator simplex -
      barycentricEdgeSubdivisionHomotopyMorphism
        (SphereSingularChainComplex.d 2 1 (simplexGenerator simplex))
  rw [barycentricTriangleSubdivisionMorphism_simplexGenerator,
    boundary_simplexGenerator, map_sum]
  simp only [map_smul,
    barycentricEdgeSubdivisionHomotopyMorphism_simplexGenerator,
    barycentricTriangleSubdivision, barycentricEdgeSubdivisionHomotopy]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]

/-- The explicit common-apex three-current attached to one addressed parent triangle. -/
abbrev barycentricDegreeTwoHomotopy (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.X 3 :=
  sourceTriangleConeRealization simplex sourceBarycentricResidual

/-- Its boundary is the complete recursive defect, with all side faces discharged by source-level
closedness. -/
theorem boundary_barycentricDegreeTwoHomotopy (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2 (barycentricDegreeTwoHomotopy simplex) =
      barycentricTriangleHomotopyDefectMorphism (simplexGenerator simplex) := by
  rw [barycentricDegreeTwoHomotopy,
    boundary_sourceTriangleConeRealization_sourceBarycentricResidual_eq_realization,
    sourceTriangleRealization_sourceBarycentricResidual]

/-- Coproduct-linear extension of the explicit degree-two source cone. -/
private def barycentricDegreeTwoHomotopyComponent (simplex : SphereSingularSimplex 2) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 3 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • barycentricDegreeTwoHomotopy simplex
      map_add' := fun left right => add_smul left right _
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply]
        exact smul_assoc scalar coefficient (barycentricDegreeTwoHomotopy simplex) }

abbrev barycentricDegreeTwoHomotopyMorphism :
    SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 3 :=
  Limits.Sigma.desc fun simplex =>
    barycentricDegreeTwoHomotopyComponent simplex

@[simp]
theorem barycentricDegreeTwoHomotopyMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 2) :
    barycentricDegreeTwoHomotopyMorphism (simplexGenerator simplex) =
      barycentricDegreeTwoHomotopy simplex := by
  have hι := Limits.Sigma.ι_desc
    (fun source => barycentricDegreeTwoHomotopyComponent source) simplex
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => barycentricDegreeTwoHomotopyComponent source))
      (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- The formerly conditional `P₂∂ = R₂` square is now inhabited by the source-faithful affine
cone. -/
theorem barycentricDegreeTwoHomotopyMorphism_comp_boundary :
    barycentricDegreeTwoHomotopyMorphism ≫
        SphereSingularChainComplex.d 3 2 =
      barycentricTriangleHomotopyDefectMorphism := by
  apply Limits.Sigma.hom_ext
  intro simplex
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change (barycentricDegreeTwoHomotopyMorphism ≫ SphereSingularChainComplex.d 3 2)
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex) coefficient) =
    barycentricTriangleHomotopyDefectMorphism
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex) coefficient)
  rw [Holonics.Hodge.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
  rw [ModuleCat.comp_apply, map_smul, barycentricDegreeTwoHomotopyMorphism_simplexGenerator,
    map_smul, boundary_barycentricDegreeTwoHomotopy, map_smul]

/-- The exact degree-two filling required by the recursive barycentric chain homotopy. -/
def barycentricDegreeTwoFilling :
    HodgeBarycentricSubdivisionHomotopy.BarycentricDegreeTwoFilling where
  fill := barycentricDegreeTwoHomotopyMorphism
  boundary := barycentricDegreeTwoHomotopyMorphism_comp_boundary

/-- The resulting degree-three current is now unconditional and satisfies the exact recursive
chain square with the six-cell barycentric degree-two current. -/
def recursiveBarycentricDegreeThreeMorphism :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 3 :=
  barycentricDegreeTwoFilling.correctedDegreeThreeMorphism

theorem recursiveBarycentricDegreeThreeMorphism_comp_boundary :
    recursiveBarycentricDegreeThreeMorphism ≫
        SphereSingularChainComplex.d 3 2 =
      SphereSingularChainComplex.d 3 2 ≫
        barycentricTriangleSubdivisionMorphism :=
  barycentricDegreeTwoFilling.correctedDegreeThreeMorphism_comp_boundary

/-! ## The producing common-apex current and its next-degree consumer -/

/-- The earlier sixteen-occurrence candidate is exactly the source-current cone already proved
in this owner. The equality retains every addressed base map and coefficient. -/
theorem commonApexResidualCone_eq_sourceTriangleConeRealization
    (simplex : SphereSingularSimplex 2) :
    commonApexResidualCone simplex =
      sourceTriangleConeRealization simplex sourceBarycentricResidual := by
  rw [commonApexResidualCone, sourceBarycentricResidual]
  simp only [map_sub, map_sum, map_smul, sourceTriangleGenerator,
    sourceTriangleConeRealization_single, one_smul]

/-- The actual candidate returns the complete degree-two recursive defect. This consumes the
source-level boundary proof rather than assuming a filling. -/
theorem boundary_commonApexResidualCone
    (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2 (commonApexResidualCone simplex) =
      barycentricTriangleHomotopyDefectMorphism (simplexGenerator simplex) := by
  rw [commonApexResidualCone_eq_sourceTriangleConeRealization]
  exact boundary_barycentricDegreeTwoHomotopy simplex

/-- The next actual cycle to be coned uses the geometrically shrinking twenty-four-cell
tetrahedron refinement and the acquired degree-two affine source homotopy. -/
def barycentricTetrahedronHomotopyDefectMorphism :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 3 :=
  HodgeBarycentricTetrahedron.barycentricTetrahedronSubdivisionMorphism - 𝟙 _ -
    SphereSingularChainComplex.d 3 2 ≫ barycentricDegreeTwoHomotopyMorphism

/-- The retained degree-three singular residual is closed. No degree-three filling or global
sphere contraction is assumed. -/
theorem barycentricTetrahedronHomotopyDefectMorphism_comp_boundary :
    barycentricTetrahedronHomotopyDefectMorphism ≫
        SphereSingularChainComplex.d 3 2 = 0 := by
  rw [barycentricTetrahedronHomotopyDefectMorphism,
    Preadditive.sub_comp, Preadditive.sub_comp,
    HodgeBarycentricTetrahedron.barycentricTetrahedronSubdivisionMorphism_comp_boundary,
    Category.id_comp, Category.assoc,
    barycentricDegreeTwoHomotopyMorphism_comp_boundary,
    barycentricTriangleHomotopyDefectMorphism,
    Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, SphereSingularChainComplex.d_comp_d,
    CategoryTheory.Limits.zero_comp]
  module

/-- Every actual tetrahedral chain therefore returns the closed next-degree residual which a
source-domain degree-four cone must fill before the sphere H4 construction can advance. -/
theorem boundary_barycentricTetrahedronHomotopyDefect
    (chain : SphereSingularChainComplex.X 3) :
    SphereSingularChainComplex.d 3 2
        (barycentricTetrahedronHomotopyDefectMorphism chain) = 0 := by
  simpa using congrArg
    (fun morphism : SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 2 =>
      morphism chain)
    barycentricTetrahedronHomotopyDefectMorphism_comp_boundary

/-! ## Exact source falsifier: vertex sampling needs the affine hypothesis -/

/-- For an arbitrary continuous base the sampled cone returns its affine vertex interpolant.
It returns the whole base only after that base has been shown affine. -/
theorem coneOverTriangleMap_face_zero_vertexInterpolation
    (base : C(Triangle, Triangle)) :
    (coneOverTriangleMap base).comp (simplexFaceMap (degree := 2) 0) =
      triangleAffineMap (fun vertex : Fin 3 => base (stdSimplex.vertex vertex)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 0 point vertex *
      coneOverTriangleVertices base vertex coordinate) =
    ∑ vertex : Fin 3, point vertex * base (stdSimplex.vertex vertex) coordinate
  fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.sum_univ_three]

/-- A continuous source triangle whose first coordinate is the square of the input coordinate.
Its remaining mass is carried exactly in the second coordinate. -/
def nonlinearTriangleSource : C(Triangle, Triangle) where
  toFun point :=
    ⟨![point 0 ^ 2, 1 - point 0 ^ 2, 0], by
      constructor
      · intro coordinate
        have lower := stdSimplex.zero_le point (0 : Fin 3)
        have upper := stdSimplex.le_one point (0 : Fin 3)
        have squareBound : point (0 : Fin 3) ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg lower (sub_nonneg.mpr upper)]
        fin_cases coordinate
        · change (0 : ℝ) ≤ point (0 : Fin 3) ^ 2
          exact sq_nonneg _
        · change (0 : ℝ) ≤ 1 - point (0 : Fin 3) ^ 2
          exact sub_nonneg.mpr squareBound
        · change (0 : ℝ) ≤ 0
          exact le_rfl
      · rw [Fin.sum_univ_three]
        simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro coordinate
    have firstCoordinate : Continuous (fun point : Triangle => point (0 : Fin 3)) :=
      (continuous_apply (0 : Fin 3)).comp continuous_subtype_val
    fin_cases coordinate
    · exact firstCoordinate.pow 2
    · exact continuous_const.sub (firstCoordinate.pow 2)
    · exact continuous_const

/-- The exact midpoint of the first two source vertices. -/
def nonlinearTriangleTestPoint : Triangle :=
  ⟨![(1 / 2 : ℝ), 1 / 2, 0], by
    constructor
    · intro coordinate
      fin_cases coordinate
      · change (0 : ℝ) ≤ 1 / 2
        norm_num
      · change (0 : ℝ) ≤ 1 / 2
        norm_num
      · change (0 : ℝ) ≤ 0
        exact le_rfl
    · rw [Fin.sum_univ_three]
      change (1 / 2 : ℝ) + 1 / 2 + 0 = 1
      norm_num⟩

theorem nonlinearTriangleSource_test_coordinate :
    nonlinearTriangleSource nonlinearTriangleTestPoint 0 = (1 / 4 : ℝ) := by
  change (1 / 2 : ℝ) ^ 2 = 1 / 4
  norm_num

theorem sampledCone_test_coordinate :
    ((coneOverTriangleMap nonlinearTriangleSource).comp
      (simplexFaceMap (degree := 2) 0)) nonlinearTriangleTestPoint 0 =
        (1 / 2 : ℝ) := by
  rw [coneOverTriangleMap_face_zero_vertexInterpolation]
  change (∑ vertex : Fin 3, nonlinearTriangleTestPoint vertex *
      nonlinearTriangleSource (stdSimplex.vertex vertex) (0 : Fin 3)) = (1 / 2 : ℝ)
  rw [Fin.sum_univ_three]
  change (1 / 2 : ℝ) * 1 ^ 2 + (1 / 2 : ℝ) * 0 ^ 2 + 0 * 0 ^ 2 = 1 / 2
  norm_num

/-- The unqualified exterior-face assertion fails on the exact polynomial source. The retained
sampling defect is one quarter in the first coordinate. -/
theorem coneOverTriangleMap_nonlinear_face_zero_ne :
    (coneOverTriangleMap nonlinearTriangleSource).comp
        (simplexFaceMap (degree := 2) 0) ≠ nonlinearTriangleSource := by
  intro equality
  have coordinateEquality := congrArg
    (fun chart : C(Triangle, Triangle) => chart nonlinearTriangleTestPoint 0) equality
  rw [sampledCone_test_coordinate, nonlinearTriangleSource_test_coordinate] at coordinateEquality
  norm_num at coordinateEquality

/-- An exact receipt for the failure of arbitrary continuous vertex sampling. -/
theorem sampledCone_test_defect :
    ((coneOverTriangleMap nonlinearTriangleSource).comp
        (simplexFaceMap (degree := 2) 0)) nonlinearTriangleTestPoint 0 -
      nonlinearTriangleSource nonlinearTriangleTestPoint 0 = (1 / 4 : ℝ) := by
  rw [sampledCone_test_coordinate, nonlinearTriangleSource_test_coordinate]
  norm_num


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_sourceTriangleConeRealization_single_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.residualPrismBase_eq_triangleAffineMap_vertices
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_sourceTriangleConeRealization_sourceBarycentricResidual_eq_realization
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_barycentricDegreeTwoHomotopy
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.barycentricDegreeTwoHomotopyMorphism_comp_boundary
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.recursiveBarycentricDegreeThreeMorphism_comp_boundary
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.commonApexResidualCone_eq_sourceTriangleConeRealization
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_commonApexResidualCone
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.barycentricTetrahedronHomotopyDefectMorphism_comp_boundary
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_barycentricTetrahedronHomotopyDefect
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.coneOverTriangleMap_face_zero_vertexInterpolation
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.nonlinearTriangleSource_test_coordinate
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sampledCone_test_coordinate
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.coneOverTriangleMap_nonlinear_face_zero_ne
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sampledCone_test_defect
