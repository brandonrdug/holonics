import HolonicsResearch.Hodge.HodgeAffineFourResidualSource

/-!
# The complete affine five-current returns R4.

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

/-! ### An actual degree-five cone returning the complete affine R4 -/

abbrev SourceFiveSimplex := stdSimplex ℝ (Fin 6)
abbrev SourceConedFourChain := C(SourceFiveSimplex, SourceFourSimplex) →₀ ℚ

def fiveSimplexToFourAffineMap (vertices : Fin 6 → SourceFourSimplex) :
    C(SourceFiveSimplex, SourceFourSimplex) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 6, point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex) (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 5, ∑ vertex : Fin 6, point vertex * vertices vertex coordinate =
            ∑ vertex : Fin 6, ∑ coordinate : Fin 5,
              point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 6, point vertex * 1 := by
          apply Finset.sum_congr rfl
          intro vertex _
          rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
        _ = 1 := by simp [stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun coordinate =>
      continuous_finset_sum _ fun vertex _ =>
        ((continuous_apply vertex).comp continuous_subtype_val).mul continuous_const

@[simp] theorem fiveSimplexToFourAffineMap_apply (vertices : Fin 6 → SourceFourSimplex)
    (point : SourceFiveSimplex) (coordinate : Fin 5) :
    fiveSimplexToFourAffineMap vertices point coordinate =
      ∑ vertex : Fin 6, point vertex * vertices vertex coordinate := rfl

@[simp] theorem fourSimplexAffineMap_apply (vertices : Fin 5 → SourceFourSimplex)
    (point : SourceFourSimplex) (coordinate : Fin 5) :
    fourSimplexAffineMap vertices point coordinate =
      ∑ vertex : Fin 5, point vertex * vertices vertex coordinate := rfl

@[simp] theorem fourSimplexAffineMap_vertex (vertices : Fin 5 → SourceFourSimplex) (vertex : Fin 5) :
    fourSimplexAffineMap vertices (stdSimplex.vertex vertex) = vertices vertex := by
  apply stdSimplex.ext
  funext coordinate
  rw [fourSimplexAffineMap_apply, sourceSumFive]
  fin_cases vertex <;> simp

def coneOverFourVertices (base : C(SourceFourSimplex, SourceFourSimplex)) : Fin 6 → SourceFourSimplex :=
  Fin.cases fourSimplexBarycenter fun vertex : Fin 5 => base (stdSimplex.vertex vertex)

def coneOverFourMap (base : C(SourceFourSimplex, SourceFourSimplex)) :
    C(SourceFiveSimplex, SourceFourSimplex) := fiveSimplexToFourAffineMap (coneOverFourVertices base)

theorem coneOverFourMap_face_zero_affine (vertices : Fin 5 → SourceFourSimplex) :
    (coneOverFourMap (fourSimplexAffineMap vertices)).comp
        (simplexFaceMap (degree := 4) 0) = fourSimplexAffineMap vertices := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 6, simplexFaceMap (degree := 4) 0 point vertex *
      coneOverFourVertices (fourSimplexAffineMap vertices) vertex coordinate) =
    ∑ vertex : Fin 5, point vertex * vertices vertex coordinate
  rw [sourceSimplexFace_weighted_sum]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [Fin.zero_succAbove, coneOverFourVertices]
  simp only [Fin.cases_succ, fourSimplexAffineMap_vertex]

theorem coneOverFourMap_face_succ (base : C(SourceFourSimplex, SourceFourSimplex))
    (omitted : Fin 5) :
    (coneOverFourMap base).comp (simplexFaceMap (degree := 4) omitted.succ) =
      fourSourceConeMap (base.comp (simplexFaceMap (degree := 3) omitted)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 6, simplexFaceMap (degree := 4) omitted.succ point vertex *
      coneOverFourVertices base vertex coordinate) =
    ∑ vertex : Fin 5, point vertex *
      (Fin.cases fourSimplexBarycenter (fun vertex : Fin 4 =>
        (base.comp (simplexFaceMap (degree := 3) omitted)) (stdSimplex.vertex vertex)) :
        Fin 5 → SourceFourSimplex) vertex coordinate
  rw [sourceSimplexFace_weighted_sum]
  apply Finset.sum_congr rfl
  intro vertex _
  exact congrArg (fun target : SourceFourSimplex => point vertex * target coordinate)
    (sourceConeVertices_face_succ fourSimplexBarycenter base omitted vertex)

def sourceFourHomotopyCone : SourceFourCellChain →ₗ[ℚ] SourceConedFourChain :=
  Finsupp.linearCombination ℚ fun base => Finsupp.single (coneOverFourMap base) 1

def sourceConedFourBoundary : SourceConedFourChain →ₗ[ℚ] SourceFourCellChain :=
  Finsupp.linearCombination ℚ fun base =>
    ∑ face : Fin 6, (-1 : ℚ) ^ (face : ℕ) •
      Finsupp.single (base.comp (simplexFaceMap (degree := 4) face)) 1

/-- Every side remains in the source return.  Exterior equality requires a complete affine base. -/
theorem sourceConedFourBoundary_cone_affine (vertices : Fin 5 → SourceFourSimplex) :
    sourceConedFourBoundary
        (sourceFourHomotopyCone (Finsupp.single (fourSimplexAffineMap vertices) 1)) =
      Finsupp.single (fourSimplexAffineMap vertices) 1 -
        sourceFourCone (sourceFourBoundary (Finsupp.single (fourSimplexAffineMap vertices) 1)) := by
  classical
  simp only [sourceFourHomotopyCone, sourceConedFourBoundary,
    Finsupp.linearCombination_single, one_smul, sourceFourBoundary]
  rw [Fin.sum_univ_succ, coneOverFourMap_face_zero_affine]
  simp_rw [coneOverFourMap_face_succ]
  simp only [map_sum, map_smul, sourceFourCone, Finsupp.linearCombination_single, one_smul]
  repeat rw [sourceSumFive]
  norm_num
  module

theorem fourSimplexAffineMap_canonicalVertices :
    fourSimplexAffineMap (fun vertex : Fin 5 => stdSimplex.vertex vertex) =
      ContinuousMap.id SourceFourSimplex := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  fin_cases coordinate <;> simp [fourSimplexAffineMap_apply, sourceSumFive]

/-- Even an arbitrary continuous lower base produces a complete affine cone before transport. -/
theorem transportedTetrahedronCone_eq_fourAffine (outerFace : Fin 5)
    (base : C(Tetrahedron, Tetrahedron)) :
    (simplexFaceMap (degree := 3) outerFace).comp (coneOverTetrahedronMap base) =
      fourSimplexAffineMap (fun vertex : Fin 5 =>
        simplexFaceMap (degree := 3) outerFace (coneOverTetrahedronVertices base vertex)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change simplexFaceMap (degree := 3) outerFace (coneOverTetrahedronMap base point) coordinate =
    ∑ vertex : Fin 5, point vertex *
      simplexFaceMap (degree := 3) outerFace (coneOverTetrahedronVertices base vertex) coordinate
  exact sourceSimplexFace_affine_sum outerFace (coneOverTetrahedronMap base point)
    (fun vertex => point vertex) (coneOverTetrahedronVertices base)
    (fun _ => fourSimplexToTetrahedronAffineMap_apply (coneOverTetrahedronVertices base) point _)
    coordinate

def sourceFourHomotopyConeReturnDefect : SourceFourCellChain →ₗ[ℚ] SourceFourCellChain :=
  sourceConedFourBoundary.comp sourceFourHomotopyCone - LinearMap.id +
    sourceFourCone.comp sourceFourBoundary

theorem sourceFourHomotopyConeReturnDefect_affine (vertices : Fin 5 → SourceFourSimplex) :
    sourceFourHomotopyConeReturnDefect (Finsupp.single (fourSimplexAffineMap vertices) 1) = 0 := by
  change sourceConedFourBoundary
      (sourceFourHomotopyCone (Finsupp.single (fourSimplexAffineMap vertices) 1)) -
    Finsupp.single (fourSimplexAffineMap vertices) 1 +
      sourceFourCone (sourceFourBoundary (Finsupp.single (fourSimplexAffineMap vertices) 1)) = 0
  rw [sourceConedFourBoundary_cone_affine]
  module

theorem sourceFourHomotopyConeReturnDefect_subdivision :
    sourceFourHomotopyConeReturnDefect sourceFourSubdivision = 0 := by
  classical
  simp only [sourceFourSubdivision, sourceFourExteriorSubdivision, sourceFourCone,
    map_sum, map_smul, sourceTetrahedronSubdivision, sourceFourFaceTransport,
    sourceTetrahedronGenerator, Finsupp.linearCombination_single, one_smul, fourSourceConeMap]
  simp only [sourceFourHomotopyConeReturnDefect_affine, smul_zero, Finset.sum_const_zero]

theorem sourceFourHomotopyConeReturnDefect_homotopyFace (outerFace : Fin 5)
    (current : SourceTetrahedronChain) :
    sourceFourHomotopyConeReturnDefect
      (sourceFourHomotopyFaceTransport outerFace (sourceTetrahedronCone current)) = 0 := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright, add_zero]
  | single base coefficient =>
      simp only [sourceTetrahedronCone, sourceFourHomotopyFaceTransport, map_smul,
        Finsupp.linearCombination_single, one_smul]
      rw [transportedTetrahedronCone_eq_fourAffine,
        sourceFourHomotopyConeReturnDefect_affine, smul_zero]

theorem sourceFourHomotopyConeReturnDefect_residual :
    sourceFourHomotopyConeReturnDefect sourceFourResidual = 0 := by
  classical
  have hid : sourceFourHomotopyConeReturnDefect
      (Finsupp.single (ContinuousMap.id SourceFourSimplex) 1) = 0 := by
    simpa only [fourSimplexAffineMap_canonicalVertices] using
      sourceFourHomotopyConeReturnDefect_affine (fun vertex : Fin 5 => stdSimplex.vertex vertex)
  simp only [sourceFourResidual, map_sub, map_sum, map_smul,
    sourceFourHomotopyConeReturnDefect_subdivision, hid,
    sourceFourHomotopyConeReturnDefect_homotopyFace, smul_zero,
    Finset.sum_const_zero, sub_self]

/-- The complete 566-term five-current returns the free residual before reception. -/
theorem sourceConedFourBoundary_sourceFourHomotopyCone_residual :
    sourceConedFourBoundary (sourceFourHomotopyCone sourceFourResidual) = sourceFourResidual := by
  have hreturn := sourceFourHomotopyConeReturnDefect_residual
  change sourceConedFourBoundary (sourceFourHomotopyCone sourceFourResidual) -
    sourceFourResidual + sourceFourCone (sourceFourBoundary sourceFourResidual) = 0 at hreturn
  rw [sourceFourBoundary_sourceFourResidual, map_zero, add_zero] at hreturn
  exact sub_eq_zero.mp hreturn


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.coneOverFourMap_face_zero_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.coneOverFourMap_face_succ
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceConedFourBoundary_cone_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourHomotopyConeReturnDefect_residual
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceConedFourBoundary_sourceFourHomotopyCone_residual
