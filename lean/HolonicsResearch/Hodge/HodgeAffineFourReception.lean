import HolonicsResearch.Hodge.HodgeAffineFourSourceBoundary

/-!
# The geometric degree-four boundary is received.

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

def fourParentSourceCell (simplex : SphereSingularSimplex 4)
    (base : C(stdSimplex ℝ (Fin 5), stdSimplex ℝ (Fin 5))) : SphereSingularSimplex 4 :=
  (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4))).symm
    ((TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4)) simplex).comp base)

def fourParentSourceFace (simplex : SphereSingularSimplex 4)
    (base : C(Tetrahedron, stdSimplex ℝ (Fin 5))) : SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 3))).symm
    ((TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4)) simplex).comp base)

def sourceFourRealization (simplex : SphereSingularSimplex 4) :
    SourceFourCellChain →ₗ[ℚ] SphereSingularChainComplex.X 4 :=
  Finsupp.linearCombination ℚ fun base => simplexGenerator (fourParentSourceCell simplex base)

def sourceFourFaceRealization (simplex : SphereSingularSimplex 4) :
    SourceFourFaceChain →ₗ[ℚ] SphereSingularChainComplex.X 3 :=
  Finsupp.linearCombination ℚ fun base => simplexGenerator (fourParentSourceFace simplex base)

theorem fourParentSourceCell_face (simplex : SphereSingularSimplex 4)
    (base : C(stdSimplex ℝ (Fin 5), stdSimplex ℝ (Fin 5))) (face : Fin 5) :
    simplexFace face (fourParentSourceCell simplex base) =
      fourParentSourceFace simplex (base.comp (simplexFaceMap (degree := 3) face)) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 3))).injective
  rw [simplexFace_realization]
  simp only [fourParentSourceCell, fourParentSourceFace, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc]

theorem boundary_sourceFourRealization (simplex : SphereSingularSimplex 4)
    (current : SourceFourCellChain) :
    SphereSingularChainComplex.d 4 3 (sourceFourRealization simplex current) =
      sourceFourFaceRealization simplex (sourceFourBoundary current) := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp only [sourceFourRealization, Finsupp.linearCombination_single, map_smul,
        boundary_simplexGenerator, fourParentSourceCell_face, sourceFourBoundary]
      simp only [Finsupp.linearCombination_single, map_smul, map_sum,
        sourceFourFaceRealization, Finsupp.linearCombination_single, one_smul]

theorem fourParentSourceFace_transport (simplex : SphereSingularSimplex 4)
    (outerFace : Fin 5) (base : C(Tetrahedron, Tetrahedron)) :
    fourParentSourceFace simplex ((simplexFaceMap (degree := 3) outerFace).comp base) =
      reparameterizedTetrahedron base (simplexFace outerFace simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 3))).injective
  simp only [fourParentSourceFace, reparameterizedTetrahedron, Equiv.apply_symm_apply]
  rw [simplexFace_realization, ContinuousMap.comp_assoc]

theorem sourceFourFaceRealization_transport (simplex : SphereSingularSimplex 4)
    (outerFace : Fin 5) (current : SourceTetrahedronChain) :
    sourceFourFaceRealization simplex (sourceFourFaceTransport outerFace current) =
      sourceTetrahedronRealization (simplexFace outerFace simplex) current := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp [sourceFourFaceRealization, sourceFourFaceTransport,
        fourParentSourceFace_transport, sourceTetrahedronRealization_single]

/-- The actual geometric receiver, with the complete 120 source cells retained. -/
def geometricBarycentricFourSubdivision (simplex : SphereSingularSimplex 4) :
    SphereSingularChainComplex.X 4 := sourceFourRealization simplex sourceFourSubdivision

/-- Concrete consumer equation: the exterior is the existing 24-cell refinement on each face. -/
theorem boundary_geometricBarycentricFourSubdivision (simplex : SphereSingularSimplex 4) :
    SphereSingularChainComplex.d 4 3 (geometricBarycentricFourSubdivision simplex) =
      barycentricTetrahedronSubdivisionMorphism
        (SphereSingularChainComplex.d 4 3 (simplexGenerator simplex)) := by
  classical
  rw [geometricBarycentricFourSubdivision, boundary_sourceFourRealization,
    sourceFourBoundary_subdivision, sourceFourExteriorSubdivision]
  simp only [map_sum, map_smul, sourceFourFaceRealization_transport,
    sourceTetrahedronRealization_subdivision]
  rw [boundary_simplexGenerator, map_sum]
  simp only [map_smul, barycentricTetrahedronSubdivisionMorphism_simplexGenerator]

private def geometricBarycentricFourComponent (simplex : SphereSingularSimplex 4) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 4 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • geometricBarycentricFourSubdivision simplex
      map_add' := fun left right => add_smul left right _
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply]
        exact smul_assoc scalar coefficient (geometricBarycentricFourSubdivision simplex) }

def geometricBarycentricDegreeFourMorphism :
    SphereSingularChainComplex.X 4 ⟶ SphereSingularChainComplex.X 4 :=
  Limits.Sigma.desc fun simplex => geometricBarycentricFourComponent simplex

@[simp] theorem geometricBarycentricDegreeFourMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 4) :
    geometricBarycentricDegreeFourMorphism (simplexGenerator simplex) =
      geometricBarycentricFourSubdivision simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 4 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => geometricBarycentricFourComponent source)) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

theorem geometricBarycentricDegreeFourMorphism_comp_boundary :
    geometricBarycentricDegreeFourMorphism ≫ SphereSingularChainComplex.d 4 3 =
      SphereSingularChainComplex.d 4 3 ≫ barycentricTetrahedronSubdivisionMorphism := by
  apply Limits.Sigma.hom_ext
  intro simplex
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change (geometricBarycentricDegreeFourMorphism ≫ SphereSingularChainComplex.d 4 3)
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 4 => rationalCoefficient) simplex) coefficient) =
    (SphereSingularChainComplex.d 4 3 ≫ barycentricTetrahedronSubdivisionMorphism)
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 4 => rationalCoefficient) simplex) coefficient)
  rw [Holonics.Hodge.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
  rw [ModuleCat.comp_apply, map_smul, geometricBarycentricDegreeFourMorphism_simplexGenerator,
    map_smul, boundary_geometricBarycentricFourSubdivision]
  rw [ModuleCat.comp_apply, map_smul, map_smul]


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_sourceFourRealization
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_geometricBarycentricFourSubdivision
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.geometricBarycentricDegreeFourMorphism_comp_boundary
