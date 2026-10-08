import HolonicsResearch.Hodge.HodgeAffineTetrahedronConeSource

/-!
# The actual degree-three receiving square.

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

def conedTetrahedronSourceSubsimplex (base : C(SourceFourSimplex, Tetrahedron))
    (simplex : SphereSingularSimplex 3) : SphereSingularSimplex 4 :=
  (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4))).symm
    ((TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 3)) simplex).comp base)

def sourceConedTetrahedronRealization (simplex : SphereSingularSimplex 3) :
    SourceConedTetrahedronChain →ₗ[ℚ] SphereSingularChainComplex.X 4 :=
  Finsupp.linearCombination ℚ fun base => simplexGenerator (conedTetrahedronSourceSubsimplex base simplex)

@[simp] theorem sourceConedTetrahedronRealization_single (simplex : SphereSingularSimplex 3)
    (base : C(SourceFourSimplex, Tetrahedron)) (coefficient : ℚ) :
    sourceConedTetrahedronRealization simplex (Finsupp.single base coefficient) =
      coefficient • simplexGenerator (conedTetrahedronSourceSubsimplex base simplex) := by
  simp [sourceConedTetrahedronRealization]

theorem conedTetrahedronSourceSubsimplex_face (base : C(SourceFourSimplex, Tetrahedron))
    (simplex : SphereSingularSimplex 3) (face : Fin 5) :
    simplexFace face (conedTetrahedronSourceSubsimplex base simplex) =
      reparameterizedTetrahedron (base.comp (simplexFaceMap (degree := 3) face)) simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).injective
  rw [simplexFace_realization]
  simp only [conedTetrahedronSourceSubsimplex, reparameterizedTetrahedron,
    Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc]

/-- Reception commutes with the complete source boundary.  It is only applied after free filling. -/
theorem boundary_sourceConedTetrahedronRealization (simplex : SphereSingularSimplex 3)
    (current : SourceConedTetrahedronChain) :
    SphereSingularChainComplex.d 4 3 (sourceConedTetrahedronRealization simplex current) =
      sourceTetrahedronRealization simplex (sourceConedTetrahedronBoundary current) := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp only [sourceConedTetrahedronRealization_single, map_smul,
        boundary_simplexGenerator, conedTetrahedronSourceSubsimplex_face,
        sourceConedTetrahedronBoundary, Finsupp.linearCombination_single]
      simp only [map_smul, map_sum, sourceTetrahedronGenerator,
        sourceTetrahedronRealization_single, one_smul]

/-- The eighty-nine four-simplex cones attached to one actual parent tetrahedron. -/
def barycentricDegreeThreeHomotopy (simplex : SphereSingularSimplex 3) :
    SphereSingularChainComplex.X 4 :=
  sourceConedTetrahedronRealization simplex (sourceTetrahedronCone sourceTetrahedronResidual)

/-- The actual consumer equation: `∂₄P₃ = Sd₃ − id − P₂∂₃`, with no sphere contraction. -/
theorem boundary_barycentricDegreeThreeHomotopy (simplex : SphereSingularSimplex 3) :
    SphereSingularChainComplex.d 4 3 (barycentricDegreeThreeHomotopy simplex) =
      barycentricTetrahedronHomotopyDefectMorphism (simplexGenerator simplex) := by
  rw [barycentricDegreeThreeHomotopy, boundary_sourceConedTetrahedronRealization,
    sourceConedTetrahedronBoundary_sourceTetrahedronCone_residual,
    sourceTetrahedronRealization_residual]

private def barycentricDegreeThreeHomotopyComponent (simplex : SphereSingularSimplex 3) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 4 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • barycentricDegreeThreeHomotopy simplex
      map_add' := fun left right => add_smul left right _
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply]
        exact smul_assoc scalar coefficient (barycentricDegreeThreeHomotopy simplex) }

abbrev barycentricDegreeThreeHomotopyMorphism :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 4 :=
  Limits.Sigma.desc fun simplex => barycentricDegreeThreeHomotopyComponent simplex

@[simp] theorem barycentricDegreeThreeHomotopyMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 3) :
    barycentricDegreeThreeHomotopyMorphism (simplexGenerator simplex) =
      barycentricDegreeThreeHomotopy simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => barycentricDegreeThreeHomotopyComponent source))
      (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- Coproduct linearity preserves the producing four-current boundary for every input. -/
theorem barycentricDegreeThreeHomotopyMorphism_comp_boundary :
    barycentricDegreeThreeHomotopyMorphism ≫ SphereSingularChainComplex.d 4 3 =
      barycentricTetrahedronHomotopyDefectMorphism := by
  apply Limits.Sigma.hom_ext
  intro simplex
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change (barycentricDegreeThreeHomotopyMorphism ≫ SphereSingularChainComplex.d 4 3)
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex) coefficient) =
    barycentricTetrahedronHomotopyDefectMorphism
      ((Limits.Sigma.ι
        (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex) coefficient)
  rw [Holonics.Hodge.HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
  rw [ModuleCat.comp_apply, map_smul, barycentricDegreeThreeHomotopyMorphism_simplexGenerator,
    map_smul, boundary_barycentricDegreeThreeHomotopy, map_smul]

/-- Complete degree-three homotopy square, joined to the acquired degree-two operator. -/
theorem barycentricDegreeThreeHomotopy_square :
    barycentricDegreeThreeHomotopyMorphism ≫ SphereSingularChainComplex.d 4 3 +
      SphereSingularChainComplex.d 3 2 ≫ barycentricDegreeTwoHomotopyMorphism =
      barycentricTetrahedronSubdivisionMorphism - 𝟙 _ := by
  rw [barycentricDegreeThreeHomotopyMorphism_comp_boundary,
    barycentricTetrahedronHomotopyDefectMorphism]
  module

/-- The algebraic degree-four continuation of the existing recursive chain square.
This operator has no geometric shrinkage claim; the actual 120-cell refinement remains owed. -/
def recursiveBarycentricDegreeFourMorphism :
    SphereSingularChainComplex.X 4 ⟶ SphereSingularChainComplex.X 4 :=
  𝟙 _ + SphereSingularChainComplex.d 4 3 ≫ barycentricDegreeThreeHomotopyMorphism

theorem recursiveBarycentricDegreeFourMorphism_comp_boundary :
    recursiveBarycentricDegreeFourMorphism ≫ SphereSingularChainComplex.d 4 3 =
      SphereSingularChainComplex.d 4 3 ≫ barycentricTetrahedronSubdivisionMorphism := by
  rw [recursiveBarycentricDegreeFourMorphism, Preadditive.add_comp, Category.id_comp,
    Category.assoc, barycentricDegreeThreeHomotopyMorphism_comp_boundary,
    barycentricTetrahedronHomotopyDefectMorphism, Preadditive.comp_sub,
    Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    SphereSingularChainComplex.d_comp_d, CategoryTheory.Limits.zero_comp]
  module


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_sourceConedTetrahedronRealization
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.boundary_barycentricDegreeThreeHomotopy
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.barycentricDegreeThreeHomotopyMorphism_comp_boundary
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.barycentricDegreeThreeHomotopy_square
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.recursiveBarycentricDegreeFourMorphism_comp_boundary
