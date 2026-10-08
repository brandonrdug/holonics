import HolonicsResearch.Hodge.HodgeAffineTriangleConeSource

/-!
# The tetrahedron residual closes before reception.

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

/-- Free currents on the actual tetrahedron source and its triangular faces. -/
abbrev SourceTetrahedronChain := C(Tetrahedron, Tetrahedron) →₀ ℚ
abbrev SourceTetrahedronFaceChain := C(Triangle, Tetrahedron) →₀ ℚ

def sourceTetrahedronGenerator (base : C(Tetrahedron, Tetrahedron)) : SourceTetrahedronChain :=
  Finsupp.single base 1

def sourceTetrahedronFaceGenerator (base : C(Triangle, Tetrahedron)) :
    SourceTetrahedronFaceChain := Finsupp.single base 1

def sourceTetrahedronBoundary : SourceTetrahedronChain →ₗ[ℚ] SourceTetrahedronFaceChain :=
  Finsupp.linearCombination ℚ fun base =>
    ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
      sourceTetrahedronFaceGenerator (base.comp (simplexFaceMap (degree := 2) face))

/-- Postcompose a retained source triangle or cone with one addressed tetrahedral face. -/
def sourceFaceTriangleTransport (outerFace : Fin 4) :
    SourceTriangleChain →ₗ[ℚ] SourceTetrahedronFaceChain :=
  Finsupp.linearCombination ℚ fun base => sourceTetrahedronFaceGenerator
    ((simplexFaceMap (degree := 2) outerFace).comp base)

def sourceFaceConeTransport (outerFace : Fin 4) :
    SourceConedTriangleChain →ₗ[ℚ] SourceTetrahedronChain :=
  Finsupp.linearCombination ℚ fun base => sourceTetrahedronGenerator
    ((simplexFaceMap (degree := 2) outerFace).comp base)

@[simp] theorem sourceTetrahedronBoundary_single
    (base : C(Tetrahedron, Tetrahedron)) (coefficient : ℚ) :
    sourceTetrahedronBoundary (Finsupp.single base coefficient) =
      coefficient • ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
        sourceTetrahedronFaceGenerator (base.comp (simplexFaceMap (degree := 2) face)) := by
  simp [sourceTetrahedronBoundary]

/-- Source restriction commutes with this actual face transport. -/
theorem sourceTetrahedronBoundary_faceConeTransport
    (outerFace : Fin 4) (current : SourceConedTriangleChain) :
    sourceTetrahedronBoundary (sourceFaceConeTransport outerFace current) =
      sourceFaceTriangleTransport outerFace (sourceConedTriangleBoundary current) := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp [sourceFaceConeTransport, sourceFaceTriangleTransport,
        sourceTetrahedronGenerator, sourceTetrahedronFaceGenerator,
        sourceTriangleGenerator, sourceConedTriangleBoundary_single,
        sourceTetrahedronBoundary_single, ContinuousMap.comp_assoc]

def sourceTriangleSubdivision : SourceTriangleChain :=
  ∑ outerFace : Fin 3, ∑ half : Fin 2,
    (-1 : ℚ) ^ ((outerFace : ℕ) + (half : ℕ)) •
      sourceTriangleGenerator (barycentricTriangleMap outerFace half)

def sourceTrianglePrismBoundary : SourceTriangleChain :=
  ∑ outerFace : Fin 3, (-1 : ℚ) ^ (outerFace : ℕ) •
    (sourceTriangleGenerator (residualPrismBase outerFace 0) -
      sourceTriangleGenerator (residualPrismBase outerFace 1) -
      sourceTriangleGenerator (residualPrismBase outerFace 2))

theorem sourceBarycentricResidual_eq_subdivision_sub_prism :
    sourceBarycentricResidual = sourceTriangleSubdivision -
      sourceTriangleGenerator (ContinuousMap.id Triangle) - sourceTrianglePrismBoundary := rfl

/-- The existing twenty-four geometric flag maps, now retained before reception. -/
def sourceTetrahedronSubdivision : SourceTetrahedronChain :=
  ∑ outerFace : Fin 4, ∑ innerFace : Fin 3, ∑ half : Fin 2,
    (-1 : ℚ) ^ ((outerFace : ℕ) + (innerFace : ℕ) + (half : ℕ)) •
      sourceTetrahedronGenerator (barycentricTetrahedronMap outerFace innerFace half)

/-- The thirty-six internal pairs cancel as actual source maps. -/
theorem sourceTetrahedronBoundary_subdivision :
    sourceTetrahedronBoundary sourceTetrahedronSubdivision =
      ∑ outerFace : Fin 4, (-1 : ℚ) ^ (outerFace : ℕ) •
        sourceFaceTriangleTransport outerFace sourceTriangleSubdivision := by
  classical
  rw [sourceTetrahedronSubdivision]
  simp only [map_sum, map_smul, sourceTetrahedronGenerator,
    sourceTetrahedronBoundary_single, one_smul]
  repeat rw [Fin.sum_univ_four]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  repeat rw [Fin.sum_univ_four]
  simp_rw [barycentricTetrahedronMap_face_zero, barycentricTetrahedronMap_half_pair,
    barycentricTetrahedronMap_radial_two, barycentricTetrahedronMap_radial_one,
    barycentricTetrahedronMap_radial_zero, barycentricTetrahedronMap_outer_01,
    barycentricTetrahedronMap_outer_02, barycentricTetrahedronMap_outer_03,
    barycentricTetrahedronMap_outer_12, barycentricTetrahedronMap_outer_13,
    barycentricTetrahedronMap_outer_23]
  simp only [sourceTriangleSubdivision, map_sum, map_smul, sourceTriangleGenerator,
    sourceFaceTriangleTransport, Finsupp.linearCombination_single, one_smul]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  norm_num
  module

/-- `24 + 1 + 4·16 = 89` addressed terms, retaining every edge-prism population. -/
def sourceTetrahedronResidual : SourceTetrahedronChain :=
  sourceTetrahedronSubdivision - sourceTetrahedronGenerator (ContinuousMap.id Tetrahedron) -
    ∑ outerFace : Fin 4, (-1 : ℚ) ^ (outerFace : ℕ) •
      sourceFaceConeTransport outerFace (sourceTriangleCone sourceBarycentricResidual)

/-- After the free cone return, the remaining boundary is the complete double-face prism. -/
theorem sourceTetrahedronBoundary_residual_eq_doublePrism :
    sourceTetrahedronBoundary sourceTetrahedronResidual =
      ∑ outerFace : Fin 4, (-1 : ℚ) ^ (outerFace : ℕ) •
        sourceFaceTriangleTransport outerFace sourceTrianglePrismBoundary := by
  classical
  have hcone (outerFace : Fin 4) :
      sourceTetrahedronBoundary
          (sourceFaceConeTransport outerFace (sourceTriangleCone sourceBarycentricResidual)) =
        sourceFaceTriangleTransport outerFace sourceBarycentricResidual :=
    (sourceTetrahedronBoundary_faceConeTransport outerFace
      (sourceTriangleCone sourceBarycentricResidual)).trans
      (congrArg (sourceFaceTriangleTransport outerFace)
        sourceConedTriangleBoundary_sourceTriangleCone_residual)
  have hid (outerFace : Fin 4) :
      sourceFaceTriangleTransport outerFace (sourceTriangleGenerator (ContinuousMap.id Triangle)) =
        sourceTetrahedronFaceGenerator (simplexFaceMap (degree := 2) outerFace) := by
    simp only [sourceFaceTriangleTransport, sourceTriangleGenerator,
      Finsupp.linearCombination_single, one_smul, ContinuousMap.comp_id]
  have hidentity :
      sourceTetrahedronBoundary (sourceTetrahedronGenerator (ContinuousMap.id Tetrahedron)) =
        ∑ outerFace : Fin 4, (-1 : ℚ) ^ (outerFace : ℕ) •
          sourceFaceTriangleTransport outerFace
            (sourceTriangleGenerator (ContinuousMap.id Triangle)) := by
    change sourceTetrahedronBoundary (Finsupp.single (ContinuousMap.id Tetrahedron) 1) = _
    rw [sourceTetrahedronBoundary_single, one_smul]
    simp only [ContinuousMap.id_comp, hid]
  rw [sourceTetrahedronResidual, map_sub, map_sub,
    sourceTetrahedronBoundary_subdivision, hidentity]
  simp only [map_sum, map_smul, hcone]
  simp only [sourceBarycentricResidual_eq_subdivision_sub_prism, map_sub]
  repeat rw [Fin.sum_univ_four]
  module

def sourceTetrahedronDoubleFace (outerFace : Fin 4) (innerFace : Fin 3) :
    C(Segment, Tetrahedron) :=
  (simplexFaceMap (degree := 2) outerFace).comp (simplexFaceMap (degree := 1) innerFace)

/-- Equality of omitted-vertex words gives equality of the whole addressed edge maps. -/
theorem sourceTetrahedronDoubleFace_eq_of_omission
    (leftOuter rightOuter : Fin 4) (leftInner rightInner : Fin 3)
    (homission : leftOuter.succAbove ∘ leftInner.succAbove =
      rightOuter.succAbove ∘ rightInner.succAbove) :
    sourceTetrahedronDoubleFace leftOuter leftInner =
      sourceTetrahedronDoubleFace rightOuter rightInner := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map (SimplexCategory.δ leftOuter).toOrderHom
      (stdSimplex.map (SimplexCategory.δ leftInner).toOrderHom point) =
    stdSimplex.map (SimplexCategory.δ rightOuter).toOrderHom
      (stdSimplex.map (SimplexCategory.δ rightInner).toOrderHom point)
  simp only [SimplexCategory.δ]
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have hmap :
      (SimplexCategory.Hom.toOrderHom
        (SimplexCategory.mkHom leftOuter.succAboveOrderEmb.toOrderHom)) ∘
        (SimplexCategory.Hom.toOrderHom
          (SimplexCategory.mkHom leftInner.succAboveOrderEmb.toOrderHom)) =
      (SimplexCategory.Hom.toOrderHom
        (SimplexCategory.mkHom rightOuter.succAboveOrderEmb.toOrderHom)) ∘
        (SimplexCategory.Hom.toOrderHom
          (SimplexCategory.mkHom rightInner.succAboveOrderEmb.toOrderHom)) := by
    funext vertex
    have hvertex := congrFun homission vertex
    simpa only [SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply] using hvertex
  rw [hmap]

theorem sourceTetrahedronDoubleFace_01 :
    sourceTetrahedronDoubleFace 0 0 = sourceTetrahedronDoubleFace 1 0 := by
  apply sourceTetrahedronDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl

theorem sourceTetrahedronDoubleFace_02 :
    sourceTetrahedronDoubleFace 0 1 = sourceTetrahedronDoubleFace 2 0 := by
  apply sourceTetrahedronDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl

theorem sourceTetrahedronDoubleFace_03 :
    sourceTetrahedronDoubleFace 0 2 = sourceTetrahedronDoubleFace 3 0 := by
  apply sourceTetrahedronDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl

theorem sourceTetrahedronDoubleFace_12 :
    sourceTetrahedronDoubleFace 1 1 = sourceTetrahedronDoubleFace 2 1 := by
  apply sourceTetrahedronDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl

theorem sourceTetrahedronDoubleFace_13 :
    sourceTetrahedronDoubleFace 1 2 = sourceTetrahedronDoubleFace 3 1 := by
  apply sourceTetrahedronDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl

theorem sourceTetrahedronDoubleFace_23 :
    sourceTetrahedronDoubleFace 2 2 = sourceTetrahedronDoubleFace 3 2 := by
  apply sourceTetrahedronDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl

/-- The reversed and constant prism members cancel with the same full parametrization. -/
theorem sourceFaceTriangleTransport_prism (outerFace : Fin 4) (innerFace : Fin 3)
    (kind : Fin 3) :
    sourceFaceTriangleTransport outerFace (sourceTriangleGenerator (residualPrismBase innerFace kind)) =
      sourceTetrahedronFaceGenerator
        ((sourceTetrahedronDoubleFace outerFace innerFace).comp
          (match kind with
          | 0 => edgeHomotopyMainMap
          | 1 => edgeHomotopyFoldMap
          | _ => edgeHomotopyConstantMap)) := by
  fin_cases kind <;>
    simp only [sourceFaceTriangleTransport, sourceTriangleGenerator,
      Finsupp.linearCombination_single, one_smul, residualPrismBase, sourceTetrahedronDoubleFace] <;>
    rfl

/-- Source closedness is proved before any possibly non-injective parent simplex is applied. -/
theorem sourceTetrahedronBoundary_sourceTetrahedronResidual :
    sourceTetrahedronBoundary sourceTetrahedronResidual = 0 := by
  classical
  rw [sourceTetrahedronBoundary_residual_eq_doublePrism]
  simp only [sourceTrianglePrismBoundary, map_sum, map_smul, map_sub,
    sourceFaceTriangleTransport_prism]
  repeat rw [Fin.sum_univ_four]
  repeat rw [Fin.sum_univ_three]
  simp_rw [sourceTetrahedronDoubleFace_01, sourceTetrahedronDoubleFace_02,
    sourceTetrahedronDoubleFace_03, sourceTetrahedronDoubleFace_12,
    sourceTetrahedronDoubleFace_13, sourceTetrahedronDoubleFace_23]
  norm_num
  module

/-! ### Reception joins this same source to the accepted degree-three consumer -/

def reparameterizedTetrahedron (base : C(Tetrahedron, Tetrahedron))
    (simplex : SphereSingularSimplex 3) : SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 3))).symm
    ((TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk 3)) simplex).comp base)

def sourceTetrahedronRealization (simplex : SphereSingularSimplex 3) :
    SourceTetrahedronChain →ₗ[ℚ] SphereSingularChainComplex.X 3 :=
  Finsupp.linearCombination ℚ fun base => simplexGenerator (reparameterizedTetrahedron base simplex)

@[simp] theorem sourceTetrahedronRealization_single (simplex : SphereSingularSimplex 3)
    (base : C(Tetrahedron, Tetrahedron)) (coefficient : ℚ) :
    sourceTetrahedronRealization simplex (Finsupp.single base coefficient) =
      coefficient • simplexGenerator (reparameterizedTetrahedron base simplex) := by
  simp [sourceTetrahedronRealization]

theorem reparameterizedTetrahedron_id (simplex : SphereSingularSimplex 3) :
    reparameterizedTetrahedron (ContinuousMap.id Tetrahedron) simplex = simplex := by
  simp [reparameterizedTetrahedron]

theorem reparameterizedTetrahedron_faceCone (outerFace : Fin 4)
    (base : C(Triangle, Triangle)) (simplex : SphereSingularSimplex 3) :
    reparameterizedTetrahedron
        ((simplexFaceMap (degree := 2) outerFace).comp (coneOverTriangleMap base)) simplex =
      conedTriangleSubsimplex base (simplexFace outerFace simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).injective
  simp only [reparameterizedTetrahedron, conedTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [simplexFace_realization, ContinuousMap.comp_assoc]

/-- This face transport is the producing cone of the parent face, with its full source. -/
theorem sourceTetrahedronRealization_faceCone (outerFace : Fin 4)
    (simplex : SphereSingularSimplex 3) (current : SourceTriangleChain) :
    sourceTetrahedronRealization simplex
        (sourceFaceConeTransport outerFace (sourceTriangleCone current)) =
      sourceTriangleConeRealization (simplexFace outerFace simplex) current := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp [sourceFaceConeTransport, sourceTriangleCone_single,
        sourceTetrahedronGenerator, sourceTetrahedronRealization_single,
        reparameterizedTetrahedron_faceCone, sourceTriangleConeRealization_single]

theorem sourceTetrahedronRealization_subdivision (simplex : SphereSingularSimplex 3) :
    sourceTetrahedronRealization simplex sourceTetrahedronSubdivision =
      barycentricTetrahedronSubdivision simplex := by
  simp [sourceTetrahedronSubdivision, sourceTetrahedronGenerator,
    barycentricTetrahedronSubdivision, reparameterizedTetrahedron,
    barycentricTetrahedronSubsimplex]

/-- The new free residual is exactly the existing actual `Sd₃ − id − P₂∂₃` consumer. -/
theorem sourceTetrahedronRealization_residual (simplex : SphereSingularSimplex 3) :
    sourceTetrahedronRealization simplex sourceTetrahedronResidual =
      barycentricTetrahedronHomotopyDefectMorphism (simplexGenerator simplex) := by
  classical
  rw [sourceTetrahedronResidual, map_sub, map_sub,
    sourceTetrahedronRealization_subdivision]
  simp only [sourceTetrahedronGenerator, sourceTetrahedronRealization_single,
    one_smul, reparameterizedTetrahedron_id, map_sum, map_smul,
    sourceTetrahedronRealization_faceCone]
  rw [barycentricTetrahedronHomotopyDefectMorphism]
  change _ = barycentricTetrahedronSubdivisionMorphism (simplexGenerator simplex) -
    simplexGenerator simplex - barycentricDegreeTwoHomotopyMorphism
      (SphereSingularChainComplex.d 3 2 (simplexGenerator simplex))
  rw [barycentricTetrahedronSubdivisionMorphism_simplexGenerator,
    boundary_simplexGenerator, map_sum]
  simp only [map_smul, barycentricDegreeTwoHomotopyMorphism_simplexGenerator,
    barycentricDegreeTwoHomotopy]


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceTetrahedronBoundary_faceConeTransport
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceTetrahedronBoundary_subdivision
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceTetrahedronBoundary_sourceTetrahedronResidual
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceTetrahedronRealization_residual
