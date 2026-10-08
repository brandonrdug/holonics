import HolonicsResearch.Hodge.HodgeAffineFourConeSource

/-!
# The canonical receiving entry assembles the source owners and reads the P4 homotopy/cycle square.

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

open Holonics.Hodge.HodgeTetrahedralStellarSubdivision
open Holonics.Hodge.HodgeBarycentricTetrahedron

/-! ### Reception consumes the producing cone and returns the actual degree-four square -/

def conedFourSourceSubsimplex (base : C(SourceFiveSimplex, SourceFourSimplex))
    (simplex : SphereSingularSimplex 4) : SphereSingularSimplex 5 :=
  (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 5))).symm
    ((TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4)) simplex).comp base)

def sourceConedFourRealization (simplex : SphereSingularSimplex 4) :
    SourceConedFourChain →ₗ[ℚ] SphereSingularChainComplex.X 5 :=
  Finsupp.linearCombination ℚ fun base => simplexGenerator (conedFourSourceSubsimplex base simplex)

@[simp] theorem sourceConedFourRealization_single (simplex : SphereSingularSimplex 4)
    (base : C(SourceFiveSimplex, SourceFourSimplex)) (coefficient : ℚ) :
    sourceConedFourRealization simplex (Finsupp.single base coefficient) =
      coefficient • simplexGenerator (conedFourSourceSubsimplex base simplex) := by
  simp [sourceConedFourRealization]

theorem conedFourSourceSubsimplex_face (base : C(SourceFiveSimplex, SourceFourSimplex))
    (simplex : SphereSingularSimplex 4) (face : Fin 6) :
    simplexFace face (conedFourSourceSubsimplex base simplex) =
      fourParentSourceCell simplex (base.comp (simplexFaceMap (degree := 4) face)) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4))).injective
  rw [simplexFace_realization]
  simp only [conedFourSourceSubsimplex, fourParentSourceCell, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc]

theorem boundary_sourceConedFourRealization (simplex : SphereSingularSimplex 4)
    (current : SourceConedFourChain) :
    SphereSingularChainComplex.d 5 4 (sourceConedFourRealization simplex current) =
      sourceFourRealization simplex (sourceConedFourBoundary current) := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp only [sourceConedFourRealization_single, map_smul, boundary_simplexGenerator,
        conedFourSourceSubsimplex_face, sourceConedFourBoundary, Finsupp.linearCombination_single]
      simp only [map_smul, map_sum, sourceFourRealization,
        Finsupp.linearCombination_single, one_smul]

def geometricBarycentricDegreeFourHomotopy (simplex : SphereSingularSimplex 4) :
    SphereSingularChainComplex.X 5 :=
  sourceConedFourRealization simplex (sourceFourHomotopyCone sourceFourResidual)

theorem boundary_geometricBarycentricDegreeFourHomotopy (simplex : SphereSingularSimplex 4) :
    SphereSingularChainComplex.d 5 4 (geometricBarycentricDegreeFourHomotopy simplex) =
      geometricBarycentricFourHomotopyDefectMorphism (simplexGenerator simplex) := by
  rw [geometricBarycentricDegreeFourHomotopy, boundary_sourceConedFourRealization,
    sourceConedFourBoundary_sourceFourHomotopyCone_residual, sourceFourRealization_residual]

private def geometricBarycentricDegreeFourHomotopyComponent (simplex : SphereSingularSimplex 4) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 5 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • geometricBarycentricDegreeFourHomotopy simplex
      map_add' := fun left right => add_smul left right _
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply]
        exact smul_assoc scalar coefficient (geometricBarycentricDegreeFourHomotopy simplex) }

def geometricBarycentricDegreeFourHomotopyMorphism :
    SphereSingularChainComplex.X 4 ⟶ SphereSingularChainComplex.X 5 :=
  Limits.Sigma.desc fun simplex => geometricBarycentricDegreeFourHomotopyComponent simplex

@[simp] theorem geometricBarycentricDegreeFourHomotopyMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 4) :
    geometricBarycentricDegreeFourHomotopyMorphism (simplexGenerator simplex) =
      geometricBarycentricDegreeFourHomotopy simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 4 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => geometricBarycentricDegreeFourHomotopyComponent source))
      (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

theorem geometricBarycentricDegreeFourHomotopyMorphism_comp_boundary :
    geometricBarycentricDegreeFourHomotopyMorphism ≫ SphereSingularChainComplex.d 5 4 =
      geometricBarycentricFourHomotopyDefectMorphism := by
  apply Limits.Sigma.hom_ext
  intro simplex
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change (geometricBarycentricDegreeFourHomotopyMorphism ≫ SphereSingularChainComplex.d 5 4)
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 4 => rationalCoefficient) simplex) coefficient) =
    geometricBarycentricFourHomotopyDefectMorphism
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 4 => rationalCoefficient) simplex) coefficient)
  rw [Holonics.Hodge.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
  rw [ModuleCat.comp_apply, map_smul,
    geometricBarycentricDegreeFourHomotopyMorphism_simplexGenerator,
    map_smul, boundary_geometricBarycentricDegreeFourHomotopy, map_smul]

/-- Actual geometric degree-four homotopy square, with the already constructed P3 consumer. -/
theorem geometricBarycentricDegreeFourHomotopy_square :
    geometricBarycentricDegreeFourHomotopyMorphism ≫ SphereSingularChainComplex.d 5 4 +
      SphereSingularChainComplex.d 4 3 ≫ barycentricDegreeThreeHomotopyMorphism =
      geometricBarycentricDegreeFourMorphism - 𝟙 _ := by
  rw [geometricBarycentricDegreeFourHomotopyMorphism_comp_boundary,
    geometricBarycentricFourHomotopyDefectMorphism]
  module

/-- The actual five-chain closes the subdivision difference of every rational four-cycle. -/
theorem geometricBarycentricDegreeFourHomotopy_cycle (current : SphereSingularChainComplex.X 4)
    (hclosed : SphereSingularChainComplex.d 4 3 current = 0) :
    SphereSingularChainComplex.d 5 4 (geometricBarycentricDegreeFourHomotopyMorphism current) =
      geometricBarycentricDegreeFourMorphism current - current := by
  have hreturn := congrArg (fun morphism => morphism current)
    geometricBarycentricDegreeFourHomotopyMorphism_comp_boundary
  rw [geometricBarycentricFourHomotopyDefectMorphism] at hreturn
  change SphereSingularChainComplex.d 5 4
      (geometricBarycentricDegreeFourHomotopyMorphism current) =
    geometricBarycentricDegreeFourMorphism current - current -
      barycentricDegreeThreeHomotopyMorphism (SphereSingularChainComplex.d 4 3 current) at hreturn
  simpa only [hclosed, map_zero, sub_zero] using hreturn

section Audit

#print axioms sourceBoundary_sourceBarycentricResidual
#print axioms boundary_sourceTriangleConeRealization_single_affine
#print axioms residualPrismBase_eq_triangleAffineMap_vertices
#print axioms boundary_sourceTriangleConeRealization_sourceBarycentricResidual_eq_realization
#print axioms boundary_barycentricDegreeTwoHomotopy
#print axioms barycentricDegreeTwoHomotopyMorphism_comp_boundary
#print axioms recursiveBarycentricDegreeThreeMorphism_comp_boundary

#print axioms commonApexResidualCone_eq_sourceTriangleConeRealization
#print axioms boundary_commonApexResidualCone
#print axioms barycentricTetrahedronHomotopyDefectMorphism_comp_boundary
#print axioms boundary_barycentricTetrahedronHomotopyDefect
#print axioms coneOverTriangleMap_face_zero_vertexInterpolation
#print axioms nonlinearTriangleSource_test_coordinate
#print axioms sampledCone_test_coordinate
#print axioms coneOverTriangleMap_nonlinear_face_zero_ne
#print axioms sampledCone_test_defect

#print axioms sourceConedTriangleBoundary_cone_affine
#print axioms sourceConedTriangleBoundary_sourceTriangleCone_residual
#print axioms sourceTetrahedronBoundary_faceConeTransport
#print axioms sourceTetrahedronBoundary_subdivision
#print axioms sourceTetrahedronBoundary_sourceTetrahedronResidual
#print axioms sourceTetrahedronRealization_residual
#print axioms coneOverTetrahedronMap_face_zero_affine
#print axioms coneOverTetrahedronMap_face_succ
#print axioms sourceConedTetrahedronBoundary_cone_affine
#print axioms sourceTetrahedronConeReturnDefect_residual
#print axioms sourceConedTetrahedronBoundary_sourceTetrahedronCone_residual
#print axioms boundary_sourceConedTetrahedronRealization
#print axioms boundary_barycentricDegreeThreeHomotopy
#print axioms barycentricDegreeThreeHomotopyMorphism_comp_boundary
#print axioms barycentricDegreeThreeHomotopy_square
#print axioms recursiveBarycentricDegreeFourMorphism_comp_boundary

#print axioms fourSourceConeMap_face_zero_affine
#print axioms fourSourceConeMap_face_succ
#print axioms sourceFourFaceBoundary_faceTransport
#print axioms sourceFourFaceBoundary_exteriorSubdivision
#print axioms sourceFourBoundary_cone_affine
#print axioms sourceFourConeReturnDefect_exteriorSubdivision
#print axioms sourceFourBoundary_subdivision
#print axioms boundary_sourceFourRealization
#print axioms boundary_geometricBarycentricFourSubdivision
#print axioms geometricBarycentricDegreeFourMorphism_comp_boundary

#print axioms sourceFourBoundary_homotopyFaceTransport
#print axioms sourceFourBoundary_residual_eq_doubleCone
#print axioms sourceFourDoubleConeTransport_alternating
#print axioms sourceFourBoundary_sourceFourResidual
#print axioms sourceFourRealization_homotopyFace
#print axioms sourceFourRealization_residual
#print axioms coneOverFourMap_face_zero_affine
#print axioms coneOverFourMap_face_succ
#print axioms sourceConedFourBoundary_cone_affine
#print axioms sourceFourHomotopyConeReturnDefect_residual
#print axioms sourceConedFourBoundary_sourceFourHomotopyCone_residual
#print axioms boundary_sourceConedFourRealization
#print axioms boundary_geometricBarycentricDegreeFourHomotopy
#print axioms geometricBarycentricDegreeFourHomotopyMorphism_comp_boundary
#print axioms geometricBarycentricDegreeFourHomotopy_square
#print axioms geometricBarycentricDegreeFourHomotopy_cycle

#print axioms sourceSimplexFace_coordinate
#print axioms sourceSimplexFace_vertex
#print axioms sourceSimplexFace_weighted_sum
#print axioms sourceSimplexFace_affine_sum
#print axioms sourceConeVertices_face_succ

end Audit

end Holonics.Hodge.HodgeBarycentricAffineSourceComplex
