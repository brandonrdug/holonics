import ElementaryHolonics.Millennium.HodgeTetrahedralCarrierAssembly

/-!
# The geometric star subdivision of an addressed singular triangle

The unicursal-star cancellation law has a literal two-dimensional successor.  Insert the
barycentre of the standard triangle, cone it to each oriented boundary edge, and retain all three
addressed subtriangles.  Their exterior edges return the original boundary.  Every interior spoke
occurs twice with opposite orientation.

This file constructs that subdivision as actual continuous maps of standard simplices and proves
the singular-chain boundary identity.  It is the first source-specific mechanism needed by the
tetrahedral carrier: repeated subdivision can make source occurrences subordinate to a finite
cover without changing their boundary class.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeStellarSubdivision

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle

/-- The exact equal-weight centre of the standard triangle. -/
def triangleBarycenter : Triangle :=
  ⟨fun _ => (3 : ℝ)⁻¹, by
    constructor
    · intro coordinate
      positivity
    · rw [Fin.sum_univ_three]
      norm_num⟩

@[simp]
theorem triangleBarycenter_apply (coordinate : Fin 3) :
    triangleBarycenter coordinate = (3 : ℝ)⁻¹ := rfl

/-- The affine map whose three addressed source vertices are sent to the supplied target
vertices.  The complete coordinate sum is retained, so this is a map of standard simplices rather
than an ambient-space approximation. -/
def triangleAffineMap (vertices : Fin 3 → Triangle) : C(Triangle, Triangle) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 3, point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex) (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 3, ∑ vertex : Fin 3, point vertex * vertices vertex coordinate =
            ∑ vertex : Fin 3, ∑ coordinate : Fin 3,
              point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 3, point vertex * 1 := by
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
theorem triangleAffineMap_apply (vertices : Fin 3 → Triangle) (point : Triangle)
    (coordinate : Fin 3) :
    triangleAffineMap vertices point coordinate =
      ∑ vertex : Fin 3, point vertex * vertices vertex coordinate := rfl

@[simp]
theorem triangleAffineMap_vertex (vertices : Fin 3 → Triangle) (vertex : Fin 3) :
    triangleAffineMap vertices (stdSimplex.vertex vertex) = vertices vertex := by
  apply stdSimplex.ext
  funext coordinate
  rw [triangleAffineMap_apply, Fin.sum_univ_three]
  fin_cases vertex <;> simp

/-- The addressed vertices of one stellar cone. -/
def stellarConeVertices (omitted : Fin 3) : Fin 3 → Triangle :=
  Fin.cases triangleBarycenter
    (fun edgeVertex : Fin 2 => stdSimplex.vertex (omitted.succAbove edgeVertex))

@[simp] theorem stellarConeVertices_zero (omitted : Fin 3) :
    stellarConeVertices omitted 0 = triangleBarycenter := rfl
@[simp] theorem stellarConeVertices_one (omitted : Fin 3) :
    stellarConeVertices omitted 1 = stdSimplex.vertex (omitted.succAbove 0) := rfl
@[simp] theorem stellarConeVertices_two (omitted : Fin 3) :
    stellarConeVertices omitted 2 = stdSimplex.vertex (omitted.succAbove 1) := rfl
@[simp] theorem stellarConeVertices_succ (omitted : Fin 3) (edgeVertex : Fin 2) :
    stellarConeVertices omitted edgeVertex.succ =
      stdSimplex.vertex (omitted.succAbove edgeVertex) := by
  rw [stellarConeVertices, Fin.cases_succ]

/-- The `omitted` cone has ordered vertices `[barycentre, face-vertex 0, face-vertex 1]`.
Its orientation is later multiplied by the ordinary alternating face sign. -/
def stellarConeMap (omitted : Fin 3) : C(Triangle, Triangle) :=
  triangleAffineMap (stellarConeVertices omitted)

@[simp]
theorem stellarConeMap_vertex_zero (omitted : Fin 3) :
    stellarConeMap omitted (stdSimplex.vertex 0) = triangleBarycenter := by
  simp [stellarConeMap]

@[simp]
theorem stellarConeMap_vertex_succ (omitted : Fin 3) (edgeVertex : Fin 2) :
    stellarConeMap omitted (stdSimplex.vertex edgeVertex.succ) =
      stdSimplex.vertex (omitted.succAbove edgeVertex) := by
  simp [stellarConeMap]

@[simp]
theorem simplexFaceMap_apply_missing (omitted : Fin 3)
    (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) omitted point omitted = 0 := by
  change FunOnFinite.linearMap ℝ ℝ omitted.succAbove point omitted = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove_ne]

@[simp]
theorem simplexFaceMap_apply_present (omitted : Fin 3)
    (point : stdSimplex ℝ (Fin 2)) (edgeVertex : Fin 2) :
    simplexFaceMap (degree := 1) omitted point (omitted.succAbove edgeVertex) =
      point edgeVertex := by
  change FunOnFinite.linearMap ℝ ℝ omitted.succAbove point
      (omitted.succAbove edgeVertex) = point edgeVertex
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun source : Fin 2 =>
        omitted.succAbove source = omitted.succAbove edgeVertex) = {edgeVertex} := by
    ext source
    simp [Fin.succAbove_right_injective.eq_iff]
  rw [hfilter, Finset.sum_singleton]

@[simp] theorem simplexFaceMap_zero_zero (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 0 point 0 = 0 := simplexFaceMap_apply_missing 0 point
@[simp] theorem simplexFaceMap_zero_one (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 0 point 1 = point 0 :=
  simplexFaceMap_apply_present 0 point 0
@[simp] theorem simplexFaceMap_zero_two (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 0 point 2 = point 1 :=
  simplexFaceMap_apply_present 0 point 1
@[simp] theorem simplexFaceMap_one_zero (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 1 point 0 = point 0 :=
  simplexFaceMap_apply_present 1 point 0
@[simp] theorem simplexFaceMap_one_one (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 1 point 1 = 0 := simplexFaceMap_apply_missing 1 point
@[simp] theorem simplexFaceMap_one_two (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 1 point 2 = point 1 :=
  simplexFaceMap_apply_present 1 point 1
@[simp] theorem simplexFaceMap_two_zero (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 2 point 0 = point 0 :=
  simplexFaceMap_apply_present 2 point 0
@[simp] theorem simplexFaceMap_two_one (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 2 point 1 = point 1 :=
  simplexFaceMap_apply_present 2 point 1
@[simp] theorem simplexFaceMap_two_two (point : stdSimplex ℝ (Fin 2)) :
    simplexFaceMap (degree := 1) 2 point 2 = 0 := simplexFaceMap_apply_missing 2 point

/-- Deleting the barycentre from a stellar cone returns the original addressed boundary edge. -/
theorem stellarConeMap_face_zero (omitted : Fin 3) :
    (stellarConeMap omitted).comp (simplexFaceMap (degree := 1) 0) =
      simplexFaceMap (degree := 1) omitted := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 0 point vertex *
        stellarConeVertices omitted vertex coordinate) =
    simplexFaceMap (degree := 1) omitted point coordinate
  fin_cases omitted <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_three, Fin.succAbove]

/-- The spoke from the barycentre to vertex `2` is shared by cones `0` and `1`. -/
theorem stellarConeMap_spoke_02 :
    (stellarConeMap 0).comp (simplexFaceMap (degree := 1) 1) =
      (stellarConeMap 1).comp (simplexFaceMap (degree := 1) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 1 point vertex *
        stellarConeVertices 0 vertex coordinate) =
    ∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 1 point vertex *
        stellarConeVertices 1 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_three, Fin.succAbove]

/-- The spoke from the barycentre to vertex `1` is shared by cones `0` and `2`. -/
theorem stellarConeMap_spoke_01 :
    (stellarConeMap 0).comp (simplexFaceMap (degree := 1) 2) =
      (stellarConeMap 2).comp (simplexFaceMap (degree := 1) 1) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 2 point vertex *
        stellarConeVertices 0 vertex coordinate) =
    ∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 1 point vertex *
        stellarConeVertices 2 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_three, Fin.succAbove]

/-- The spoke from the barycentre to vertex `0` is shared by cones `1` and `2`. -/
theorem stellarConeMap_spoke_00 :
    (stellarConeMap 1).comp (simplexFaceMap (degree := 1) 2) =
      (stellarConeMap 2).comp (simplexFaceMap (degree := 1) 2) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 2 point vertex *
        stellarConeVertices 1 vertex coordinate) =
    ∑ vertex : Fin 3,
      simplexFaceMap (degree := 1) 2 point vertex *
        stellarConeVertices 2 vertex coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_three, Fin.succAbove]

/-- One addressed geometric subtriangle of a singular triangle. -/
def stellarSubsimplex (omitted : Fin 3) (simplex : SphereSingularSimplex 2) :
    SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2)) simplex).comp (stellarConeMap omitted))

theorem stellarSubsimplex_face_zero (omitted : Fin 3)
    (simplex : SphereSingularSimplex 2) :
    simplexFace 0 (stellarSubsimplex omitted simplex) = simplexFace omitted simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [stellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, stellarConeMap_face_zero]

theorem stellarSubsimplex_spoke_02 (simplex : SphereSingularSimplex 2) :
    simplexFace 1 (stellarSubsimplex 0 simplex) =
      simplexFace 1 (stellarSubsimplex 1 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [stellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, stellarConeMap_spoke_02]

theorem stellarSubsimplex_spoke_01 (simplex : SphereSingularSimplex 2) :
    simplexFace 2 (stellarSubsimplex 0 simplex) =
      simplexFace 1 (stellarSubsimplex 2 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [stellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, stellarConeMap_spoke_01]

theorem stellarSubsimplex_spoke_00 (simplex : SphereSingularSimplex 2) :
    simplexFace 2 (stellarSubsimplex 1 simplex) =
      simplexFace 2 (stellarSubsimplex 2 simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [stellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, stellarConeMap_spoke_00]

/-- The oriented three-cone subdivision of one singular triangle. -/
def stellarSubdivision (simplex : SphereSingularSimplex 2) : SphereChain 2 :=
  ∑ omitted : Fin 3, (-1 : ℚ) ^ (omitted : ℕ) •
    simplexGenerator (stellarSubsimplex omitted simplex)

/-- All three interior spokes cancel and only the original exterior boundary survives. -/
theorem boundary_stellarSubdivision (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 2 1 (stellarSubdivision simplex) =
      SphereSingularChainComplex.d 2 1 (simplexGenerator simplex) := by
  rw [stellarSubdivision, map_sum]
  simp only [map_smul, boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_three]
  rw [stellarSubsimplex_face_zero 0, stellarSubsimplex_face_zero 1,
    stellarSubsimplex_face_zero 2]
  rw [stellarSubsimplex_spoke_02, stellarSubsimplex_spoke_01,
    stellarSubsimplex_spoke_00]
  norm_num
  module

/-- Coefficient transport into one subdivided singular-chain population. -/
def subdivisionCoefficient (value : SphereChain 2) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 2 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • value
      map_add' := fun left right => add_smul left right value
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
        rfl }

/-- The coproduct-linear extension of the geometric subdivision from simplex occurrences to all
rational singular two-chains. -/
def stellarSubdivisionMorphism :
    SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 2 :=
  Limits.Sigma.desc fun simplex => subdivisionCoefficient (stellarSubdivision simplex)

@[simp]
theorem stellarSubdivisionMorphism_simplexGenerator (simplex : SphereSingularSimplex 2) :
    stellarSubdivisionMorphism (simplexGenerator simplex) = stellarSubdivision simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc
          (fun source => subdivisionCoefficient (stellarSubdivision source))) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  change (1 : ℚ) • stellarSubdivision simplex = stellarSubdivision simplex
  exact one_smul ℚ _

/-- Subdivision preserves the complete exterior seam on every rational two-chain. -/
theorem stellarSubdivisionMorphism_comp_boundary :
    stellarSubdivisionMorphism ≫ SphereSingularChainComplex.d 2 1 =
      SphereSingularChainComplex.d 2 1 := by
  let left : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 1 :=
    stellarSubdivisionMorphism ≫ SphereSingularChainComplex.d 2 1
  let right : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 1 :=
    SphereSingularChainComplex.d 2 1
  have hleftRight : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change ℚ at coefficient
    simp only [left, right, ConcreteCategory.comp_apply]
    rw [HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
    change SphereSingularChainComplex.d 2 1
        (stellarSubdivisionMorphism (coefficient • simplexGenerator simplex)) =
      SphereSingularChainComplex.d 2 1 (coefficient • simplexGenerator simplex)
    simp only [map_smul, stellarSubdivisionMorphism_simplexGenerator,
      boundary_stellarSubdivision]
  exact hleftRight

theorem boundary_stellarSubdivisionMorphism (chain : SphereChain 2) :
    SphereSingularChainComplex.d 2 1 (stellarSubdivisionMorphism chain) =
      SphereSingularChainComplex.d 2 1 chain := by
  simpa only [ConcreteCategory.comp_apply] using
    congrArg (fun morphism : SphereSingularChainComplex.X 2 ⟶
      SphereSingularChainComplex.X 1 => morphism chain)
      stellarSubdivisionMorphism_comp_boundary

/-- Repeated stellar refinement.  The population grows, but every scale returns the same exterior
boundary receiver. -/
def iteratedStellarSubdivision : ℕ → SphereChain 2 → SphereChain 2
  | 0 => id
  | scale + 1 => fun chain =>
      stellarSubdivisionMorphism (iteratedStellarSubdivision scale chain)

/-- Uniform scale theorem: every finite refinement depth preserves the addressed seam exactly. -/
theorem boundary_iteratedStellarSubdivision (scale : ℕ) (chain : SphereChain 2) :
    SphereSingularChainComplex.d 2 1 (iteratedStellarSubdivision scale chain) =
      SphereSingularChainComplex.d 2 1 chain := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      rw [iteratedStellarSubdivision, boundary_stellarSubdivisionMorphism,
        inductionHypothesis]

section Audit

#print axioms triangleAffineMap_vertex
#print axioms stellarConeMap_face_zero
#print axioms stellarConeMap_spoke_02
#print axioms stellarConeMap_spoke_01
#print axioms stellarConeMap_spoke_00
#print axioms boundary_stellarSubdivision
#print axioms stellarSubdivisionMorphism_comp_boundary
#print axioms boundary_iteratedStellarSubdivision

end Audit

end Soma.Holonics.Millennium.HodgeStellarSubdivision
