import HolonicsResearch.Hodge.HodgeAffineTetrahedronResidualSource

/-!
# The complete free tetrahedron cone returns R3.

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

/-! ### The source-domain degree-four cone, with its complete side return -/

abbrev SourceFourSimplex := stdSimplex ℝ (Fin 5)
abbrev SourceConedTetrahedronChain := C(SourceFourSimplex, Tetrahedron) →₀ ℚ

/-- Five addressed vertices define a complete affine map into the source tetrahedron. -/
def fourSimplexToTetrahedronAffineMap (vertices : Fin 5 → Tetrahedron) :
    C(SourceFourSimplex, Tetrahedron) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 5, point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex) (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 4, ∑ vertex : Fin 5, point vertex * vertices vertex coordinate =
            ∑ vertex : Fin 5, ∑ coordinate : Fin 4,
              point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 5, point vertex * 1 := by
          apply Finset.sum_congr rfl
          intro vertex _
          rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
        _ = 1 := by simp [stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun coordinate =>
      continuous_finset_sum _ fun vertex _ =>
        ((continuous_apply vertex).comp continuous_subtype_val).mul continuous_const

@[simp] theorem fourSimplexToTetrahedronAffineMap_apply (vertices : Fin 5 → Tetrahedron)
    (point : SourceFourSimplex) (coordinate : Fin 4) :
    fourSimplexToTetrahedronAffineMap vertices point coordinate =
      ∑ vertex : Fin 5, point vertex * vertices vertex coordinate := rfl

def coneOverTetrahedronVertices (base : C(Tetrahedron, Tetrahedron)) : Fin 5 → Tetrahedron :=
  Fin.cases tetrahedronBarycenter fun vertex : Fin 4 => base (stdSimplex.vertex vertex)

def coneOverTetrahedronMap (base : C(Tetrahedron, Tetrahedron)) :
    C(SourceFourSimplex, Tetrahedron) :=
  fourSimplexToTetrahedronAffineMap (coneOverTetrahedronVertices base)

def commonApexTetrahedronFaceVertices (base : C(Triangle, Tetrahedron)) : Fin 4 → Tetrahedron :=
  Fin.cases tetrahedronBarycenter fun vertex : Fin 3 => base (stdSimplex.vertex vertex)

def commonApexTetrahedronFaceMap (base : C(Triangle, Tetrahedron)) :
    C(Tetrahedron, Tetrahedron) :=
  tetrahedronAffineMap (commonApexTetrahedronFaceVertices base)

/-- Exterior return requires a complete affine base, as in the accepted polynomial falsifier. -/
theorem coneOverTetrahedronMap_face_zero_affine (vertices : Fin 4 → Tetrahedron) :
    (coneOverTetrahedronMap (tetrahedronAffineMap vertices)).comp
        (simplexFaceMap (degree := 3) 0) = tetrahedronAffineMap vertices := by
  apply ContinuousMap.ext
  intro point
  have hface (face : Fin 5) (index : Fin 5) :
      simplexFaceMap (degree := 3) face point index =
        ∑ source : Fin 4, if face.succAbove source = index then point source else 0 := by
    change FunOnFinite.linearMap ℝ ℝ face.succAbove point index = _
    rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 5, simplexFaceMap (degree := 3) 0 point vertex *
      coneOverTetrahedronVertices (tetrahedronAffineMap vertices) vertex coordinate) =
    ∑ vertex : Fin 4, point vertex * vertices vertex coordinate
  rw [Fin.sum_univ_succ]
  fin_cases coordinate <;>
    simp [hface, Fin.sum_univ_four, coneOverTetrahedronVertices,
      tetrahedronAffineMap_vertex, Fin.succAbove]

theorem coneOverTetrahedronMap_face_succ (base : C(Tetrahedron, Tetrahedron)) (omitted : Fin 4) :
    (coneOverTetrahedronMap base).comp (simplexFaceMap (degree := 3) omitted.succ) =
      commonApexTetrahedronFaceMap (base.comp (simplexFaceMap (degree := 2) omitted)) := by
  apply ContinuousMap.ext
  intro point
  have hface (face : Fin 5) (index : Fin 5) :
      simplexFaceMap (degree := 3) face point index =
        ∑ source : Fin 4, if face.succAbove source = index then point source else 0 := by
    change FunOnFinite.linearMap ℝ ℝ face.succAbove point index = _
    rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  have hvertex (face : Fin 4) (vertex : Fin 3) :
      simplexFaceMap (degree := 2) face (stdSimplex.vertex vertex) =
        stdSimplex.vertex (face.succAbove vertex) := by
    change stdSimplex.map (SimplexCategory.δ face).toOrderHom
      (stdSimplex.vertex vertex) = stdSimplex.vertex (face.succAbove vertex)
    rw [stdSimplex.map_vertex]
    rfl
  have hweighted (weights : Fin 5 → ℝ) :
      (∑ index : Fin 5, simplexFaceMap (degree := 3) omitted.succ point index * weights index) =
        ∑ vertex : Fin 4, point vertex * weights (omitted.succ.succAbove vertex) := by
    simp_rw [hface]
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro vertex _
    exact Finset.sum_ite_eq_of_mem Finset.univ (omitted.succ.succAbove vertex)
      (fun index => point vertex * weights index) (Finset.mem_univ _)
  have hcarrier (vertex : Fin 4) :
      coneOverTetrahedronVertices base (omitted.succ.succAbove vertex) =
        commonApexTetrahedronFaceVertices
          (base.comp (simplexFaceMap (degree := 2) omitted)) vertex := by
    refine Fin.cases ?_ (fun source => ?_) vertex
    · rw [Fin.succ_succAbove_zero]
      rfl
    · rw [Fin.succ_succAbove_succ, coneOverTetrahedronVertices,
        commonApexTetrahedronFaceVertices, Fin.cases_succ, Fin.cases_succ,
        ContinuousMap.comp_apply, hvertex]
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 5, simplexFaceMap (degree := 3) omitted.succ point vertex *
      coneOverTetrahedronVertices base vertex coordinate) =
    ∑ vertex : Fin 4, point vertex *
      commonApexTetrahedronFaceVertices
        (base.comp (simplexFaceMap (degree := 2) omitted)) vertex coordinate
  rw [hweighted (fun vertex => coneOverTetrahedronVertices base vertex coordinate)]
  apply Finset.sum_congr rfl
  intro vertex _
  exact congrArg (fun target : Tetrahedron => point vertex * target coordinate) (hcarrier vertex)

def sourceTetrahedronCone : SourceTetrahedronChain →ₗ[ℚ] SourceConedTetrahedronChain :=
  Finsupp.linearCombination ℚ fun base => Finsupp.single (coneOverTetrahedronMap base) 1

def sourceTetrahedronFaceCone : SourceTetrahedronFaceChain →ₗ[ℚ] SourceTetrahedronChain :=
  Finsupp.linearCombination ℚ fun base =>
    sourceTetrahedronGenerator (commonApexTetrahedronFaceMap base)

def sourceConedTetrahedronBoundary : SourceConedTetrahedronChain →ₗ[ℚ] SourceTetrahedronChain :=
  Finsupp.linearCombination ℚ fun base =>
    ∑ face : Fin 5, (-1 : ℚ) ^ (face : ℕ) •
      sourceTetrahedronGenerator (base.comp (simplexFaceMap (degree := 3) face))

/-- No side face has been discarded: the free cone returns the base minus its coned boundary. -/
theorem sourceConedTetrahedronBoundary_cone_affine (vertices : Fin 4 → Tetrahedron) :
    sourceConedTetrahedronBoundary
        (sourceTetrahedronCone (sourceTetrahedronGenerator (tetrahedronAffineMap vertices))) =
      sourceTetrahedronGenerator (tetrahedronAffineMap vertices) -
        sourceTetrahedronFaceCone
          (sourceTetrahedronBoundary (sourceTetrahedronGenerator (tetrahedronAffineMap vertices))) := by
  classical
  have hcone (base : C(Tetrahedron, Tetrahedron)) :
      sourceTetrahedronCone (sourceTetrahedronGenerator base) =
        Finsupp.single (coneOverTetrahedronMap base) 1 := by
    simp only [sourceTetrahedronGenerator, sourceTetrahedronCone,
      Finsupp.linearCombination_single, one_smul]
  have hboundary (base : C(SourceFourSimplex, Tetrahedron)) :
      sourceConedTetrahedronBoundary (Finsupp.single base 1) =
        ∑ face : Fin 5, (-1 : ℚ) ^ (face : ℕ) •
          sourceTetrahedronGenerator (base.comp (simplexFaceMap (degree := 3) face)) := by
    simp only [sourceConedTetrahedronBoundary, Finsupp.linearCombination_single, one_smul]
  have hbaseBoundary :
      sourceTetrahedronBoundary (sourceTetrahedronGenerator (tetrahedronAffineMap vertices)) =
        ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
          sourceTetrahedronFaceGenerator
            ((tetrahedronAffineMap vertices).comp (simplexFaceMap (degree := 2) face)) := by
    simp only [sourceTetrahedronGenerator, sourceTetrahedronBoundary_single, one_smul]
  have hface (base : C(Triangle, Tetrahedron)) :
      sourceTetrahedronFaceCone (sourceTetrahedronFaceGenerator base) =
        sourceTetrahedronGenerator (commonApexTetrahedronFaceMap base) := by
    simp only [sourceTetrahedronFaceCone, sourceTetrahedronFaceGenerator,
      Finsupp.linearCombination_single, one_smul]
  rw [hcone, hboundary, hbaseBoundary, map_sum]
  simp only [map_smul, hface]
  rw [Fin.sum_univ_succ]
  rw [coneOverTetrahedronMap_face_zero_affine]
  simp_rw [coneOverTetrahedronMap_face_succ]
  repeat rw [Fin.sum_univ_four]
  norm_num
  module

theorem tetrahedronAffineMap_canonicalVertices :
    tetrahedronAffineMap (fun vertex : Fin 4 => stdSimplex.vertex vertex) =
      ContinuousMap.id Tetrahedron := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  fin_cases coordinate <;> simp [tetrahedronAffineMap_apply, Fin.sum_univ_four]

/-- Every transported source triangle cone is affine even for an arbitrary continuous base. -/
theorem transportedTriangleCone_eq_affine (outerFace : Fin 4) (base : C(Triangle, Triangle)) :
    (simplexFaceMap (degree := 2) outerFace).comp (coneOverTriangleMap base) =
      tetrahedronAffineMap (fun vertex : Fin 4 =>
        simplexFaceMap (degree := 2) outerFace (coneOverTriangleVertices base vertex)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change simplexFaceMap (degree := 2) outerFace (coneOverTriangleMap base point) coordinate =
    ∑ vertex : Fin 4, point vertex *
      simplexFaceMap (degree := 2) outerFace (coneOverTriangleVertices base vertex) coordinate
  fin_cases outerFace <;> fin_cases coordinate <;>
    simp [coneOverTriangleMap, tetrahedronToTriangleAffineMap_apply, Fin.sum_univ_four,
      Fin.succAbove]

/-- This exact residual vanishes on complete affine maps; it is not declared zero on all maps. -/
def sourceTetrahedronConeReturnDefect : SourceTetrahedronChain →ₗ[ℚ] SourceTetrahedronChain :=
  sourceConedTetrahedronBoundary.comp sourceTetrahedronCone - LinearMap.id +
    sourceTetrahedronFaceCone.comp sourceTetrahedronBoundary

theorem sourceTetrahedronConeReturnDefect_affine (vertices : Fin 4 → Tetrahedron) :
    sourceTetrahedronConeReturnDefect
      (sourceTetrahedronGenerator (tetrahedronAffineMap vertices)) = 0 := by
  change sourceConedTetrahedronBoundary
      (sourceTetrahedronCone (sourceTetrahedronGenerator (tetrahedronAffineMap vertices))) -
    sourceTetrahedronGenerator (tetrahedronAffineMap vertices) +
      sourceTetrahedronFaceCone
        (sourceTetrahedronBoundary (sourceTetrahedronGenerator (tetrahedronAffineMap vertices))) = 0
  rw [sourceConedTetrahedronBoundary_cone_affine]
  module

theorem sourceTetrahedronConeReturnDefect_faceCone (outerFace : Fin 4)
    (current : SourceTriangleChain) :
    sourceTetrahedronConeReturnDefect
      (sourceFaceConeTransport outerFace (sourceTriangleCone current)) = 0 := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright, add_zero]
  | single base coefficient =>
      simp only [sourceTriangleCone_single, map_smul, sourceFaceConeTransport,
        Finsupp.linearCombination_single, one_smul]
      rw [transportedTriangleCone_eq_affine, sourceTetrahedronConeReturnDefect_affine, smul_zero]

theorem sourceTetrahedronConeReturnDefect_residual :
    sourceTetrahedronConeReturnDefect sourceTetrahedronResidual = 0 := by
  classical
  have hsubdivision : sourceTetrahedronConeReturnDefect sourceTetrahedronSubdivision = 0 := by
    simp only [sourceTetrahedronSubdivision, map_sum, map_smul, barycentricTetrahedronMap]
    simp only [sourceTetrahedronConeReturnDefect_affine, smul_zero, Finset.sum_const_zero]
  have hid : sourceTetrahedronConeReturnDefect
      (sourceTetrahedronGenerator (ContinuousMap.id Tetrahedron)) = 0 := by
    simpa only [tetrahedronAffineMap_canonicalVertices] using
      sourceTetrahedronConeReturnDefect_affine (fun vertex : Fin 4 => stdSimplex.vertex vertex)
  simp only [sourceTetrahedronResidual, map_sub, map_sum, map_smul, hsubdivision, hid,
    sourceTetrahedronConeReturnDefect_faceCone, smul_zero, Finset.sum_const_zero, sub_self]

/-- The eighty-nine affine cones have their actual free four-current boundary equal to R₃. -/
theorem sourceConedTetrahedronBoundary_sourceTetrahedronCone_residual :
    sourceConedTetrahedronBoundary (sourceTetrahedronCone sourceTetrahedronResidual) =
      sourceTetrahedronResidual := by
  have hreturn := sourceTetrahedronConeReturnDefect_residual
  change sourceConedTetrahedronBoundary (sourceTetrahedronCone sourceTetrahedronResidual) -
    sourceTetrahedronResidual +
      sourceTetrahedronFaceCone (sourceTetrahedronBoundary sourceTetrahedronResidual) = 0 at hreturn
  rw [sourceTetrahedronBoundary_sourceTetrahedronResidual, map_zero, add_zero] at hreturn
  exact sub_eq_zero.mp hreturn


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.coneOverTetrahedronMap_face_zero_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.coneOverTetrahedronMap_face_succ
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceConedTetrahedronBoundary_cone_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceTetrahedronConeReturnDefect_residual
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceConedTetrahedronBoundary_sourceTetrahedronCone_residual
