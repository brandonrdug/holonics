import HolonicsResearch.Hodge.HodgeAffineFourReception

/-!
# The complete degree-four residual closes and is received.

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

/-! ### The complete degree-four residual closes in its producing source

The 120 geometric cells, the identity, and all five transported 89-term cones
remain in the free current.  No sphere receiver or cycle-filling hypothesis is
used to obtain the source boundary return.
-/

/-- Postcompose the actual degree-three producing cone with one parent face. -/
def sourceFourHomotopyFaceTransport (outerFace : Fin 5) :
    SourceConedTetrahedronChain →ₗ[ℚ] SourceFourCellChain :=
  Finsupp.linearCombination ℚ fun base =>
    Finsupp.single ((simplexFaceMap (degree := 3) outerFace).comp base) 1

theorem sourceFourBoundary_homotopyFaceTransport (outerFace : Fin 5)
    (current : SourceConedTetrahedronChain) :
    sourceFourBoundary (sourceFourHomotopyFaceTransport outerFace current) =
      sourceFourFaceTransport outerFace (sourceConedTetrahedronBoundary current) := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp [sourceFourBoundary, sourceFourHomotopyFaceTransport, sourceFourFaceTransport,
        sourceConedTetrahedronBoundary, sourceTetrahedronGenerator, ContinuousMap.comp_assoc]

def sourceFourResidual : SourceFourCellChain :=
  sourceFourSubdivision - Finsupp.single (ContinuousMap.id SourceFourSimplex) 1 -
    ∑ outerFace : Fin 5, (-1 : ℚ) ^ (outerFace : ℕ) •
      sourceFourHomotopyFaceTransport outerFace (sourceTetrahedronCone sourceTetrahedronResidual)

theorem sourceFourBoundary_identity :
    sourceFourBoundary (Finsupp.single (ContinuousMap.id SourceFourSimplex) 1) =
      ∑ outerFace : Fin 5, (-1 : ℚ) ^ (outerFace : ℕ) •
        sourceFourFaceTransport outerFace
          (sourceTetrahedronGenerator (ContinuousMap.id Tetrahedron)) := by
  simp [sourceFourBoundary, sourceFourFaceTransport, sourceTetrahedronGenerator]

/-- The only surviving population is the complete transported double-face degree-two cone. -/
theorem sourceFourBoundary_residual_eq_doubleCone :
    sourceFourBoundary sourceFourResidual =
      ∑ outerFace : Fin 5, (-1 : ℚ) ^ (outerFace : ℕ) •
        sourceFourFaceTransport outerFace
          (∑ innerFace : Fin 4, (-1 : ℚ) ^ (innerFace : ℕ) •
            sourceFaceConeTransport innerFace (sourceTriangleCone sourceBarycentricResidual)) := by
  classical
  rw [sourceFourResidual, map_sub, map_sub, sourceFourBoundary_subdivision,
    sourceFourExteriorSubdivision, sourceFourBoundary_identity]
  simp only [map_sum, map_smul, sourceFourBoundary_homotopyFaceTransport,
    sourceConedTetrahedronBoundary_sourceTetrahedronCone_residual]
  -- Consume the fixed-residual cone return before exposing that residual's three populations.
  simp only [sourceTetrahedronResidual, map_sub, map_sum, map_smul]
  repeat rw [sourceSumFive]
  module

def sourceFourDoubleConeTransport (outerFace : Fin 5) (innerFace : Fin 4) :
    SourceConedTriangleChain →ₗ[ℚ] SourceFourFaceChain :=
  Finsupp.linearCombination ℚ fun base =>
    Finsupp.single ((sourceFourDoubleFace outerFace innerFace).comp base) 1

theorem sourceFourFaceTransport_faceCone (outerFace : Fin 5) (innerFace : Fin 4)
    (current : SourceConedTriangleChain) :
    sourceFourFaceTransport outerFace (sourceFaceConeTransport innerFace current) =
      sourceFourDoubleConeTransport outerFace innerFace current := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp [sourceFourFaceTransport, sourceFaceConeTransport, sourceFourDoubleConeTransport,
        sourceTetrahedronGenerator, sourceFourDoubleFace, ContinuousMap.comp_assoc]

/-- Ten whole-map omission pairs cancel; constant and reversed bases are retained. -/
theorem sourceFourDoubleConeTransport_alternating (current : SourceConedTriangleChain) :
    (∑ outerFace : Fin 5, (-1 : ℚ) ^ (outerFace : ℕ) •
      ∑ innerFace : Fin 4, (-1 : ℚ) ^ (innerFace : ℕ) •
        sourceFourDoubleConeTransport outerFace innerFace current) = 0 := by
  classical
  rw [sourceSumFive]
  repeat rw [Fin.sum_univ_four]
  simp_rw [sourceFourDoubleConeTransport, sourceFourDoubleFace_01, sourceFourDoubleFace_02,
    sourceFourDoubleFace_03, sourceFourDoubleFace_04, sourceFourDoubleFace_12,
    sourceFourDoubleFace_13, sourceFourDoubleFace_14, sourceFourDoubleFace_23,
    sourceFourDoubleFace_24, sourceFourDoubleFace_34]
  norm_num
  module

/-- Closedness is a source law, obtained before any receiving sphere simplex is applied. -/
theorem sourceFourBoundary_sourceFourResidual : sourceFourBoundary sourceFourResidual = 0 := by
  rw [sourceFourBoundary_residual_eq_doubleCone]
  simp only [map_sum, map_smul, sourceFourFaceTransport_faceCone]
  exact sourceFourDoubleConeTransport_alternating (sourceTriangleCone sourceBarycentricResidual)

theorem fourParentSourceCell_identity (simplex : SphereSingularSimplex 4) :
    fourParentSourceCell simplex (ContinuousMap.id SourceFourSimplex) = simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4))).injective
  simp [fourParentSourceCell]

theorem fourParentSourceCell_homotopyFace (simplex : SphereSingularSimplex 4)
    (outerFace : Fin 5) (base : C(SourceFourSimplex, Tetrahedron)) :
    fourParentSourceCell simplex ((simplexFaceMap (degree := 3) outerFace).comp base) =
      conedTetrahedronSourceSubsimplex base (simplexFace outerFace simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 4))).injective
  simp only [fourParentSourceCell, conedTetrahedronSourceSubsimplex, Equiv.apply_symm_apply]
  rw [simplexFace_realization, ContinuousMap.comp_assoc]

theorem sourceFourRealization_homotopyFace (simplex : SphereSingularSimplex 4)
    (outerFace : Fin 5) (current : SourceConedTetrahedronChain) :
    sourceFourRealization simplex (sourceFourHomotopyFaceTransport outerFace current) =
      sourceConedTetrahedronRealization (simplexFace outerFace simplex) current := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp [sourceFourRealization, sourceFourHomotopyFaceTransport,
        fourParentSourceCell_homotopyFace, sourceConedTetrahedronRealization_single]

def geometricBarycentricFourHomotopyDefectMorphism :
    SphereSingularChainComplex.X 4 ⟶ SphereSingularChainComplex.X 4 :=
  geometricBarycentricDegreeFourMorphism - 𝟙 _ -
    SphereSingularChainComplex.d 4 3 ≫ barycentricDegreeThreeHomotopyMorphism

/-- The producing R4 is exactly the actual geometric receiver's missing homotopy return. -/
theorem sourceFourRealization_residual (simplex : SphereSingularSimplex 4) :
    sourceFourRealization simplex sourceFourResidual =
      geometricBarycentricFourHomotopyDefectMorphism (simplexGenerator simplex) := by
  classical
  have hid : sourceFourRealization simplex
      (Finsupp.single (ContinuousMap.id SourceFourSimplex) 1) = simplexGenerator simplex := by
    simp [sourceFourRealization, fourParentSourceCell_identity]
  rw [sourceFourResidual, map_sub, map_sub, hid]
  simp only [map_sum, map_smul, sourceFourRealization_homotopyFace]
  change geometricBarycentricFourSubdivision simplex - simplexGenerator simplex -
    (∑ outerFace : Fin 5, (-1 : ℚ) ^ (outerFace : ℕ) •
      barycentricDegreeThreeHomotopy (simplexFace outerFace simplex)) = _
  rw [geometricBarycentricFourHomotopyDefectMorphism]
  change _ = geometricBarycentricDegreeFourMorphism (simplexGenerator simplex) -
    simplexGenerator simplex - barycentricDegreeThreeHomotopyMorphism
      (SphereSingularChainComplex.d 4 3 (simplexGenerator simplex))
  rw [geometricBarycentricDegreeFourMorphism_simplexGenerator, boundary_simplexGenerator, map_sum]
  simp only [map_smul, barycentricDegreeThreeHomotopyMorphism_simplexGenerator]


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourBoundary_homotopyFaceTransport
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourBoundary_residual_eq_doubleCone
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourDoubleConeTransport_alternating
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourBoundary_sourceFourResidual
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourRealization_homotopyFace
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourRealization_residual
