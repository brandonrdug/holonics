import ElementaryHolonics.Millennium.HodgeStellarSubdivision

/-!
# The geometric stellar subdivision of an addressed singular tetrahedron

This is the degree-three successor of `HodgeStellarSubdivision`.  Four oriented tetrahedral cones
join the exact barycentre of the standard tetrahedron to its four boundary faces.  Their six
internal triangular seams occur in oppositely oriented pairs.  The resulting singular three-chain
therefore returns exactly the original exterior boundary.

The construction deliberately retains the four cone occurrences and all six pairings.  The next
recursive deed will subdivide the exterior face carriers as well, yielding the degree-three
component compatible with the checked degree-two subdivision.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision

/-- The exact equal-weight centre of the standard tetrahedron. -/
def tetrahedronBarycenter : Tetrahedron :=
  ⟨fun _ => (4 : ℝ)⁻¹, by
    constructor
    · intro coordinate
      positivity
    · rw [Fin.sum_univ_four]
      norm_num⟩

@[simp]
theorem tetrahedronBarycenter_apply (coordinate : Fin 4) :
    tetrahedronBarycenter coordinate = (4 : ℝ)⁻¹ := rfl

/-- Affine transport determined by four addressed vertices of the standard tetrahedron. -/
def tetrahedronAffineMap (vertices : Fin 4 → Tetrahedron) : C(Tetrahedron, Tetrahedron) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 4, point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex) (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 4, ∑ vertex : Fin 4, point vertex * vertices vertex coordinate =
            ∑ vertex : Fin 4, ∑ coordinate : Fin 4,
              point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 4, point vertex * 1 := by
          apply Finset.sum_congr rfl
          intro vertex _
          rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
        _ = 1 := by simp [stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun coordinate =>
      continuous_finset_sum _ fun vertex _ =>
        ((continuous_apply vertex).comp continuous_subtype_val).mul continuous_const

@[simp]
theorem tetrahedronAffineMap_apply (vertices : Fin 4 → Tetrahedron) (point : Tetrahedron)
    (coordinate : Fin 4) :
    tetrahedronAffineMap vertices point coordinate =
      ∑ vertex : Fin 4, point vertex * vertices vertex coordinate := rfl

@[simp]
theorem tetrahedronAffineMap_vertex (vertices : Fin 4 → Tetrahedron) (vertex : Fin 4) :
    tetrahedronAffineMap vertices (stdSimplex.vertex vertex) = vertices vertex := by
  apply stdSimplex.ext
  funext coordinate
  rw [tetrahedronAffineMap_apply, Fin.sum_univ_four]
  fin_cases vertex <;> simp

/-- The addressed vertices `[barycentre, face-vertex 0, face-vertex 1, face-vertex 2]`. -/
def tetrahedralConeVertices (omitted : Fin 4) : Fin 4 → Tetrahedron :=
  Fin.cases tetrahedronBarycenter
    (fun faceVertex : Fin 3 => stdSimplex.vertex (omitted.succAbove faceVertex))

@[simp] theorem tetrahedralConeVertices_zero (omitted : Fin 4) :
    tetrahedralConeVertices omitted 0 = tetrahedronBarycenter := rfl
@[simp] theorem tetrahedralConeVertices_one (omitted : Fin 4) :
    tetrahedralConeVertices omitted 1 = stdSimplex.vertex (omitted.succAbove 0) := rfl
@[simp] theorem tetrahedralConeVertices_two (omitted : Fin 4) :
    tetrahedralConeVertices omitted 2 = stdSimplex.vertex (omitted.succAbove 1) := rfl
@[simp] theorem tetrahedralConeVertices_three (omitted : Fin 4) :
    tetrahedralConeVertices omitted 3 = stdSimplex.vertex (omitted.succAbove 2) := rfl
@[simp] theorem tetrahedralConeVertices_succ (omitted : Fin 4) (faceVertex : Fin 3) :
    tetrahedralConeVertices omitted faceVertex.succ =
      stdSimplex.vertex (omitted.succAbove faceVertex) := by
  rw [tetrahedralConeVertices, Fin.cases_succ]

/-- One of the four geometric tetrahedral cones. -/
def tetrahedralConeMap (omitted : Fin 4) : C(Tetrahedron, Tetrahedron) :=
  tetrahedronAffineMap (tetrahedralConeVertices omitted)

@[simp]
theorem simplexFaceMap_three_apply_missing (omitted : Fin 4) (point : Triangle) :
    simplexFaceMap (degree := 2) omitted point omitted = 0 := by
  change FunOnFinite.linearMap ℝ ℝ omitted.succAbove point omitted = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove_ne]

@[simp]
theorem simplexFaceMap_three_apply_present (omitted : Fin 4) (point : Triangle)
    (faceVertex : Fin 3) :
    simplexFaceMap (degree := 2) omitted point (omitted.succAbove faceVertex) =
      point faceVertex := by
  change FunOnFinite.linearMap ℝ ℝ omitted.succAbove point
      (omitted.succAbove faceVertex) = point faceVertex
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun source : Fin 3 =>
        omitted.succAbove source = omitted.succAbove faceVertex) = {faceVertex} := by
    ext source
    simp [Fin.succAbove_right_injective.eq_iff]
  rw [hfilter, Finset.sum_singleton]

@[simp] theorem simplexFaceMap_three_0_0 (point : Triangle) :
    simplexFaceMap (degree := 2) 0 point 0 = 0 :=
  simplexFaceMap_three_apply_missing 0 point
@[simp] theorem simplexFaceMap_three_0_1 (point : Triangle) :
    simplexFaceMap (degree := 2) 0 point 1 = point 0 :=
  simplexFaceMap_three_apply_present 0 point 0
@[simp] theorem simplexFaceMap_three_0_2 (point : Triangle) :
    simplexFaceMap (degree := 2) 0 point 2 = point 1 :=
  simplexFaceMap_three_apply_present 0 point 1
@[simp] theorem simplexFaceMap_three_0_3 (point : Triangle) :
    simplexFaceMap (degree := 2) 0 point 3 = point 2 :=
  simplexFaceMap_three_apply_present 0 point 2
@[simp] theorem simplexFaceMap_three_1_0 (point : Triangle) :
    simplexFaceMap (degree := 2) 1 point 0 = point 0 :=
  simplexFaceMap_three_apply_present 1 point 0
@[simp] theorem simplexFaceMap_three_1_1 (point : Triangle) :
    simplexFaceMap (degree := 2) 1 point 1 = 0 :=
  simplexFaceMap_three_apply_missing 1 point
@[simp] theorem simplexFaceMap_three_1_2 (point : Triangle) :
    simplexFaceMap (degree := 2) 1 point 2 = point 1 :=
  simplexFaceMap_three_apply_present 1 point 1
@[simp] theorem simplexFaceMap_three_1_3 (point : Triangle) :
    simplexFaceMap (degree := 2) 1 point 3 = point 2 :=
  simplexFaceMap_three_apply_present 1 point 2
@[simp] theorem simplexFaceMap_three_2_0 (point : Triangle) :
    simplexFaceMap (degree := 2) 2 point 0 = point 0 :=
  simplexFaceMap_three_apply_present 2 point 0
@[simp] theorem simplexFaceMap_three_2_1 (point : Triangle) :
    simplexFaceMap (degree := 2) 2 point 1 = point 1 :=
  simplexFaceMap_three_apply_present 2 point 1
@[simp] theorem simplexFaceMap_three_2_2 (point : Triangle) :
    simplexFaceMap (degree := 2) 2 point 2 = 0 :=
  simplexFaceMap_three_apply_missing 2 point
@[simp] theorem simplexFaceMap_three_2_3 (point : Triangle) :
    simplexFaceMap (degree := 2) 2 point 3 = point 2 :=
  simplexFaceMap_three_apply_present 2 point 2
@[simp] theorem simplexFaceMap_three_3_0 (point : Triangle) :
    simplexFaceMap (degree := 2) 3 point 0 = point 0 :=
  simplexFaceMap_three_apply_present 3 point 0
@[simp] theorem simplexFaceMap_three_3_1 (point : Triangle) :
    simplexFaceMap (degree := 2) 3 point 1 = point 1 :=
  simplexFaceMap_three_apply_present 3 point 1
@[simp] theorem simplexFaceMap_three_3_2 (point : Triangle) :
    simplexFaceMap (degree := 2) 3 point 2 = point 2 :=
  simplexFaceMap_three_apply_present 3 point 2
@[simp] theorem simplexFaceMap_three_3_3 (point : Triangle) :
    simplexFaceMap (degree := 2) 3 point 3 = 0 :=
  simplexFaceMap_three_apply_missing 3 point

/-- Deleting the cone point returns the addressed exterior triangular face. -/
theorem tetrahedralConeMap_face_zero (omitted : Fin 4) :
    (tetrahedralConeMap omitted).comp (simplexFaceMap (degree := 2) 0) =
      simplexFaceMap (degree := 2) omitted := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4,
      simplexFaceMap (degree := 2) 0 point vertex *
        tetrahedralConeVertices omitted vertex coordinate) =
    simplexFaceMap (degree := 2) omitted point coordinate
  fin_cases omitted <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.succAbove]

theorem tetrahedralConeMap_pair_01 :
    (tetrahedralConeMap 0).comp (simplexFaceMap (degree := 2) 1) =
      (tetrahedralConeMap 1).comp (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      tetrahedralConeVertices 0 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      tetrahedralConeVertices 1 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_four, Fin.succAbove]

theorem tetrahedralConeMap_pair_02 :
    (tetrahedralConeMap 0).comp (simplexFaceMap (degree := 2) 2) =
      (tetrahedralConeMap 2).comp (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      tetrahedralConeVertices 0 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      tetrahedralConeVertices 2 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_four, Fin.succAbove]

theorem tetrahedralConeMap_pair_03 :
    (tetrahedralConeMap 0).comp (simplexFaceMap (degree := 2) 3) =
      (tetrahedralConeMap 3).comp (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 3 point vertex *
      tetrahedralConeVertices 0 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 1 point vertex *
      tetrahedralConeVertices 3 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_four, Fin.succAbove]

theorem tetrahedralConeMap_pair_12 :
    (tetrahedralConeMap 1).comp (simplexFaceMap (degree := 2) 2) =
      (tetrahedralConeMap 2).comp (simplexFaceMap (degree := 2) 2) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      tetrahedralConeVertices 1 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      tetrahedralConeVertices 2 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_four, Fin.succAbove]

theorem tetrahedralConeMap_pair_13 :
    (tetrahedralConeMap 1).comp (simplexFaceMap (degree := 2) 3) =
      (tetrahedralConeMap 3).comp (simplexFaceMap (degree := 2) 2) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 3 point vertex *
      tetrahedralConeVertices 1 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 2 point vertex *
      tetrahedralConeVertices 3 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_four, Fin.succAbove]

theorem tetrahedralConeMap_pair_23 :
    (tetrahedralConeMap 2).comp (simplexFaceMap (degree := 2) 3) =
      (tetrahedralConeMap 3).comp (simplexFaceMap (degree := 2) 3) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 3 point vertex *
      tetrahedralConeVertices 2 vertex coordinate) =
    ∑ vertex : Fin 4, simplexFaceMap (degree := 2) 3 point vertex *
      tetrahedralConeVertices 3 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_four, Fin.succAbove]

/-- One addressed geometric subtetrahedron of a singular three-simplex. -/
def tetrahedralStellarSubsimplex (omitted : Fin 4)
    (simplex : SphereSingularSimplex 3) : SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 3)) simplex).comp (tetrahedralConeMap omitted))

theorem tetrahedralStellarSubsimplex_face_zero (omitted : Fin 4)
    (simplex : SphereSingularSimplex 3) :
    simplexFace 0 (tetrahedralStellarSubsimplex omitted simplex) =
      simplexFace omitted simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [tetrahedralStellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, tetrahedralConeMap_face_zero]

theorem tetrahedralStellarSubsimplex_pair_01 (simplex : SphereSingularSimplex 3) :
    simplexFace 1 (tetrahedralStellarSubsimplex 0 simplex) =
      simplexFace 1 (tetrahedralStellarSubsimplex 1 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [tetrahedralStellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, tetrahedralConeMap_pair_01]

theorem tetrahedralStellarSubsimplex_pair_02 (simplex : SphereSingularSimplex 3) :
    simplexFace 2 (tetrahedralStellarSubsimplex 0 simplex) =
      simplexFace 1 (tetrahedralStellarSubsimplex 2 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [tetrahedralStellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, tetrahedralConeMap_pair_02]

theorem tetrahedralStellarSubsimplex_pair_03 (simplex : SphereSingularSimplex 3) :
    simplexFace 3 (tetrahedralStellarSubsimplex 0 simplex) =
      simplexFace 1 (tetrahedralStellarSubsimplex 3 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [tetrahedralStellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, tetrahedralConeMap_pair_03]

theorem tetrahedralStellarSubsimplex_pair_12 (simplex : SphereSingularSimplex 3) :
    simplexFace 2 (tetrahedralStellarSubsimplex 1 simplex) =
      simplexFace 2 (tetrahedralStellarSubsimplex 2 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [tetrahedralStellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, tetrahedralConeMap_pair_12]

theorem tetrahedralStellarSubsimplex_pair_13 (simplex : SphereSingularSimplex 3) :
    simplexFace 3 (tetrahedralStellarSubsimplex 1 simplex) =
      simplexFace 2 (tetrahedralStellarSubsimplex 3 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [tetrahedralStellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, tetrahedralConeMap_pair_13]

theorem tetrahedralStellarSubsimplex_pair_23 (simplex : SphereSingularSimplex 3) :
    simplexFace 3 (tetrahedralStellarSubsimplex 2 simplex) =
      simplexFace 3 (tetrahedralStellarSubsimplex 3 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [tetrahedralStellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, tetrahedralConeMap_pair_23]

/-- The signed four-cone subdivision of one singular tetrahedron. -/
def tetrahedralStellarSubdivision (simplex : SphereSingularSimplex 3) : SphereChain 3 :=
  ∑ omitted : Fin 4, (-1 : ℚ) ^ (omitted : ℕ) •
    simplexGenerator (tetrahedralStellarSubsimplex omitted simplex)

/-- The six internal triangular seams cancel and the original exterior boundary survives. -/
theorem boundary_tetrahedralStellarSubdivision (simplex : SphereSingularSimplex 3) :
    SphereSingularChainComplex.d 3 2 (tetrahedralStellarSubdivision simplex) =
      SphereSingularChainComplex.d 3 2 (simplexGenerator simplex) := by
  rw [tetrahedralStellarSubdivision, map_sum]
  simp only [map_smul, boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_four]
  rw [tetrahedralStellarSubsimplex_face_zero 0,
    tetrahedralStellarSubsimplex_face_zero 1,
    tetrahedralStellarSubsimplex_face_zero 2,
    tetrahedralStellarSubsimplex_face_zero 3]
  rw [tetrahedralStellarSubsimplex_pair_01,
    tetrahedralStellarSubsimplex_pair_02,
    tetrahedralStellarSubsimplex_pair_03,
    tetrahedralStellarSubsimplex_pair_12,
    tetrahedralStellarSubsimplex_pair_13,
    tetrahedralStellarSubsimplex_pair_23]
  norm_num
  module

/-- Linear extension of the four-cone subdivision to every singular three-chain. -/
def tetrahedralSubdivisionCoefficient (value : SphereChain 3) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 3 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • value
      map_add' := fun left right => add_smul left right _
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
        rfl }

/-- Linear extension of the four-cone subdivision to every singular three-chain. -/
def tetrahedralStellarSubdivisionMorphism :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 3 :=
  Limits.Sigma.desc fun simplex =>
    tetrahedralSubdivisionCoefficient (tetrahedralStellarSubdivision simplex)

@[simp]
theorem tetrahedralStellarSubdivisionMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 3) :
    tetrahedralStellarSubdivisionMorphism (simplexGenerator simplex) =
      tetrahedralStellarSubdivision simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source =>
          tetrahedralSubdivisionCoefficient
            (tetrahedralStellarSubdivision source))) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  change (1 : ℚ) • tetrahedralStellarSubdivision simplex = _
  exact one_smul ℚ _

theorem tetrahedralStellarSubdivisionMorphism_comp_boundary :
    tetrahedralStellarSubdivisionMorphism ≫ SphereSingularChainComplex.d 3 2 =
      SphereSingularChainComplex.d 3 2 := by
  let left : SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 2 :=
    tetrahedralStellarSubdivisionMorphism ≫ SphereSingularChainComplex.d 3 2
  let right : SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 2 :=
    SphereSingularChainComplex.d 3 2
  have hleftRight : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change ℚ at coefficient
    simp only [left, right]
    change SphereSingularChainComplex.d 3 2
        (tetrahedralStellarSubdivisionMorphism
          ((Limits.Sigma.ι
            (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex) coefficient)) =
      SphereSingularChainComplex.d 3 2
        ((Limits.Sigma.ι
          (fun _ : SphereSingularSimplex 3 => rationalCoefficient) simplex) coefficient)
    rw [HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
    change SphereSingularChainComplex.d 3 2
        (tetrahedralStellarSubdivisionMorphism (coefficient • simplexGenerator simplex)) =
      SphereSingularChainComplex.d 3 2 (coefficient • simplexGenerator simplex)
    simp only [map_smul, tetrahedralStellarSubdivisionMorphism_simplexGenerator,
      boundary_tetrahedralStellarSubdivision]
  exact hleftRight

theorem boundary_tetrahedralStellarSubdivisionMorphism (chain : SphereChain 3) :
    SphereSingularChainComplex.d 3 2 (tetrahedralStellarSubdivisionMorphism chain) =
      SphereSingularChainComplex.d 3 2 chain := by
  simpa only [ConcreteCategory.comp_apply] using
    congrArg (fun morphism : SphereSingularChainComplex.X 3 ⟶
      SphereSingularChainComplex.X 2 => morphism chain)
      tetrahedralStellarSubdivisionMorphism_comp_boundary

/-- Repeated degree-three stellar refinement. -/
def iteratedTetrahedralStellarSubdivision : ℕ → SphereChain 3 → SphereChain 3
  | 0 => id
  | scale + 1 => fun chain =>
      tetrahedralStellarSubdivisionMorphism
        (iteratedTetrahedralStellarSubdivision scale chain)

/-- Uniform scale theorem for the tetrahedral exterior seam. -/
theorem boundary_iteratedTetrahedralStellarSubdivision (scale : ℕ) (chain : SphereChain 3) :
    SphereSingularChainComplex.d 3 2
        (iteratedTetrahedralStellarSubdivision scale chain) =
      SphereSingularChainComplex.d 3 2 chain := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      rw [iteratedTetrahedralStellarSubdivision,
        boundary_tetrahedralStellarSubdivisionMorphism, inductionHypothesis]

/-- The exact obstruction to combining the basic degree-three refinement with the already checked
degree-two refinement as one chain map. -/
def recursiveSubdivisionDefect :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 2 :=
  tetrahedralStellarSubdivisionMorphism ≫ SphereSingularChainComplex.d 3 2 -
    SphereSingularChainComplex.d 3 2 ≫ stellarSubdivisionMorphism

theorem recursiveSubdivisionDefect_eq :
    recursiveSubdivisionDefect =
      SphereSingularChainComplex.d 3 2 -
        SphereSingularChainComplex.d 3 2 ≫ stellarSubdivisionMorphism := by
  rw [recursiveSubdivisionDefect, tetrahedralStellarSubdivisionMorphism_comp_boundary]

theorem recursiveSubdivisionDefect_apply (chain : SphereChain 3) :
    recursiveSubdivisionDefect chain =
      SphereSingularChainComplex.d 3 2 chain -
        stellarSubdivisionMorphism (SphereSingularChainComplex.d 3 2 chain) := by
  rw [recursiveSubdivisionDefect_eq]
  rfl

/-- The basic degree-three cones already form the desired recursive component exactly when the
degree-two refinement fixes every boundary arriving from degree three. -/
theorem recursiveSubdivisionDefect_eq_zero_iff :
    recursiveSubdivisionDefect = 0 ↔
      SphereSingularChainComplex.d 3 2 ≫ stellarSubdivisionMorphism =
        SphereSingularChainComplex.d 3 2 := by
  rw [recursiveSubdivisionDefect_eq, sub_eq_zero]
  exact eq_comm

section Audit

#print axioms tetrahedralConeMap_face_zero
#print axioms tetrahedralConeMap_pair_01
#print axioms boundary_tetrahedralStellarSubdivision
#print axioms tetrahedralStellarSubdivisionMorphism_comp_boundary
#print axioms boundary_iteratedTetrahedralStellarSubdivision
#print axioms recursiveSubdivisionDefect_eq_zero_iff

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision
