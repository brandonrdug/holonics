import ElementaryHolonics.Millennium.HodgeTetrahedralStellarSubdivision

/-!
# The explicit homotopy from stellar subdivision to the identity

The degree-two stellar subdivision and the identity have the same exterior boundary.  Their
difference is therefore a cycle supported inside the source standard triangle.  This file cones
that exact difference to the triangle barycentre and constructs a singular three-chain whose
boundary is `stellarSubdivision σ - simplexGenerator σ`.

This is the correction required to turn the basic degree-three four-cone refinement into a
recursive chain-map component satisfying `∂ S₃ = S₂ ∂`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeStellarSubdivisionHomotopy

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision
open Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision

@[simp]
theorem simplexFaceMap_vertex (omitted : Fin 3) (edgeVertex : Fin 2) :
    simplexFaceMap (degree := 1) omitted (stdSimplex.vertex edgeVertex) =
      stdSimplex.vertex (omitted.succAbove edgeVertex) := by
  apply stdSimplex.ext
  funext coordinate
  fin_cases omitted <;> fin_cases edgeVertex <;> fin_cases coordinate <;>
    simp [Fin.succAbove]

/-- An affine tetrahedron whose image lies in the standard triangle. -/
def tetrahedronToTriangleAffineMap (vertices : Fin 4 → Triangle) : C(Tetrahedron, Triangle) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 4, point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex) (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 3, ∑ vertex : Fin 4, point vertex * vertices vertex coordinate =
            ∑ vertex : Fin 4, ∑ coordinate : Fin 3,
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
theorem tetrahedronToTriangleAffineMap_apply (vertices : Fin 4 → Triangle)
    (point : Tetrahedron) (coordinate : Fin 3) :
    tetrahedronToTriangleAffineMap vertices point coordinate =
      ∑ vertex : Fin 4, point vertex * vertices vertex coordinate := rfl

/-- Cone one affine triangle map to the exact triangle barycentre. -/
def coneOverTriangleVertices (base : C(Triangle, Triangle)) : Fin 4 → Triangle :=
  Fin.cases triangleBarycenter fun vertex : Fin 3 => base (stdSimplex.vertex vertex)

@[simp] theorem coneOverTriangleVertices_zero (base : C(Triangle, Triangle)) :
    coneOverTriangleVertices base 0 = triangleBarycenter := rfl
@[simp] theorem coneOverTriangleVertices_succ (base : C(Triangle, Triangle)) (vertex : Fin 3) :
    coneOverTriangleVertices base vertex.succ = base (stdSimplex.vertex vertex) := by
  rw [coneOverTriangleVertices, Fin.cases_succ]

@[simp] theorem coneOverTriangleVertices_one (base : C(Triangle, Triangle)) :
    coneOverTriangleVertices base 1 = base (stdSimplex.vertex 0) := by
  exact coneOverTriangleVertices_succ base 0

@[simp] theorem coneOverTriangleVertices_two (base : C(Triangle, Triangle)) :
    coneOverTriangleVertices base 2 = base (stdSimplex.vertex 1) := by
  exact coneOverTriangleVertices_succ base 1

@[simp] theorem coneOverTriangleVertices_three (base : C(Triangle, Triangle)) :
    coneOverTriangleVertices base 3 = base (stdSimplex.vertex 2) := by
  exact coneOverTriangleVertices_succ base 2

def coneOverTriangleMap (base : C(Triangle, Triangle)) : C(Tetrahedron, Triangle) :=
  tetrahedronToTriangleAffineMap (coneOverTriangleVertices base)

/-- The cone over an affine stellar subtriangle returns that subtriangle on its exterior face. -/
theorem coneOverTriangleMap_face_zero_stellar (omitted : Fin 3) :
    (coneOverTriangleMap (stellarConeMap omitted)).comp
        (simplexFaceMap (degree := 2) 0) = stellarConeMap omitted := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 0 point vertex *
      coneOverTriangleVertices (stellarConeMap omitted) vertex coordinate) =
    ∑ vertex : Fin 3, point vertex * stellarConeVertices omitted vertex coordinate
  fin_cases omitted <;> fin_cases coordinate <;>
    simp [stellarConeMap, Fin.sum_univ_four,
      Fin.sum_univ_three, Fin.succAbove]

/-- The cone over the identity triangle returns the identity map on its exterior face. -/
theorem coneOverTriangleMap_face_zero_id :
    (coneOverTriangleMap (ContinuousMap.id Triangle)).comp
        (simplexFaceMap (degree := 2) 0) = ContinuousMap.id Triangle := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4, simplexFaceMap (degree := 2) 0 point vertex *
      coneOverTriangleVertices (ContinuousMap.id Triangle) vertex coordinate) = point coordinate
  fin_cases coordinate <;>
    simp [Fin.sum_univ_four]

/-- The addressed vertices of the cone over one base edge. -/
def coneOverTriangleFaceVertices (base : C(Triangle, Triangle)) (omitted : Fin 3) :
    Fin 3 → Triangle :=
  Fin.cases triangleBarycenter fun edgeVertex : Fin 2 =>
    (base.comp (simplexFaceMap (degree := 1) omitted))
      (stdSimplex.vertex edgeVertex)

@[simp] theorem coneOverTriangleFaceVertices_zero (base : C(Triangle, Triangle))
    (omitted : Fin 3) :
    coneOverTriangleFaceVertices base omitted 0 = triangleBarycenter := rfl

@[simp] theorem coneOverTriangleFaceVertices_succ (base : C(Triangle, Triangle))
    (omitted : Fin 3) (edgeVertex : Fin 2) :
    coneOverTriangleFaceVertices base omitted edgeVertex.succ =
      (base.comp (simplexFaceMap (degree := 1) omitted))
        (stdSimplex.vertex edgeVertex) := by
  rw [coneOverTriangleFaceVertices, Fin.cases_succ]

@[simp] theorem coneOverTriangleFaceVertices_one (base : C(Triangle, Triangle))
    (omitted : Fin 3) :
    coneOverTriangleFaceVertices base omitted 1 =
      (base.comp (simplexFaceMap (degree := 1) omitted))
        (stdSimplex.vertex 0) := by
  exact coneOverTriangleFaceVertices_succ base omitted 0

@[simp] theorem coneOverTriangleFaceVertices_two (base : C(Triangle, Triangle))
    (omitted : Fin 3) :
    coneOverTriangleFaceVertices base omitted 2 =
      (base.comp (simplexFaceMap (degree := 1) omitted))
        (stdSimplex.vertex 1) := by
  exact coneOverTriangleFaceVertices_succ base omitted 1

/-- The triangular face of a cone is itself the affine cone over the corresponding edge of the
base triangle.  Keeping this factorization explicit lets every checked edge identification lift
to a checked triangular seam identification. -/
def coneOverTriangleFaceMap (base : C(Triangle, Triangle)) (omitted : Fin 3) :
    C(Triangle, Triangle) :=
  triangleAffineMap (coneOverTriangleFaceVertices base omitted)

theorem coneOverTriangleMap_face_succ (base : C(Triangle, Triangle)) (omitted : Fin 3) :
    (coneOverTriangleMap base).comp
        (simplexFaceMap (degree := 2) omitted.succ) =
      coneOverTriangleFaceMap base omitted := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 4,
      simplexFaceMap (degree := 2) omitted.succ point vertex *
        coneOverTriangleVertices base vertex coordinate) =
    ∑ vertex : Fin 3, point vertex *
      coneOverTriangleFaceVertices base omitted vertex coordinate
  fin_cases omitted <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_four, Fin.sum_univ_three, Fin.succAbove]

/-- An equality of addressed base edges lifts to an equality of the corresponding cone faces. -/
theorem coneOverTriangleMap_face_eq_of_base_face_eq
    (left right : C(Triangle, Triangle)) (leftFace rightFace : Fin 3)
    (hface : left.comp (simplexFaceMap (degree := 1) leftFace) =
      right.comp (simplexFaceMap (degree := 1) rightFace)) :
    (coneOverTriangleMap left).comp
        (simplexFaceMap (degree := 2) leftFace.succ) =
      (coneOverTriangleMap right).comp
        (simplexFaceMap (degree := 2) rightFace.succ) := by
  rw [coneOverTriangleMap_face_succ, coneOverTriangleMap_face_succ,
    coneOverTriangleFaceMap, coneOverTriangleFaceMap]
  apply congrArg triangleAffineMap
  funext vertex
  fin_cases vertex
  · rfl
  · change (left.comp (simplexFaceMap (degree := 1) leftFace))
        (stdSimplex.vertex 0) =
      (right.comp (simplexFaceMap (degree := 1) rightFace))
        (stdSimplex.vertex 0)
    rw [hface]
  · change (left.comp (simplexFaceMap (degree := 1) leftFace))
        (stdSimplex.vertex 1) =
      (right.comp (simplexFaceMap (degree := 1) rightFace))
        (stdSimplex.vertex 1)
    rw [hface]

theorem coneOverTriangleMap_spoke_02 :
    (coneOverTriangleMap (stellarConeMap 0)).comp
        (simplexFaceMap (degree := 2) 2) =
      (coneOverTriangleMap (stellarConeMap 1)).comp
        (simplexFaceMap (degree := 2) 2) := by
  exact coneOverTriangleMap_face_eq_of_base_face_eq _ _ 1 1 stellarConeMap_spoke_02

theorem coneOverTriangleMap_spoke_01 :
    (coneOverTriangleMap (stellarConeMap 0)).comp
        (simplexFaceMap (degree := 2) 3) =
      (coneOverTriangleMap (stellarConeMap 2)).comp
        (simplexFaceMap (degree := 2) 2) := by
  exact coneOverTriangleMap_face_eq_of_base_face_eq _ _ 2 1 stellarConeMap_spoke_01

theorem coneOverTriangleMap_spoke_00 :
    (coneOverTriangleMap (stellarConeMap 1)).comp
        (simplexFaceMap (degree := 2) 3) =
      (coneOverTriangleMap (stellarConeMap 2)).comp
        (simplexFaceMap (degree := 2) 3) := by
  exact coneOverTriangleMap_face_eq_of_base_face_eq _ _ 2 2 stellarConeMap_spoke_00

theorem coneOverTriangleMap_exterior_zero (omitted : Fin 3) :
    (coneOverTriangleMap (stellarConeMap omitted)).comp
        (simplexFaceMap (degree := 2) 1) =
      (coneOverTriangleMap (ContinuousMap.id Triangle)).comp
        (simplexFaceMap (degree := 2) omitted.succ) := by
  apply coneOverTriangleMap_face_eq_of_base_face_eq _ _ 0 omitted
  simpa using stellarConeMap_face_zero omitted

/-- Compose a singular triangle with one geometric cone to obtain a singular tetrahedron. -/
def conedTriangleSubsimplex (base : C(Triangle, Triangle))
    (simplex : SphereSingularSimplex 2) : SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2)) simplex).comp
          (coneOverTriangleMap base))

theorem conedTriangleSubsimplex_face_zero_stellar (omitted : Fin 3)
    (simplex : SphereSingularSimplex 2) :
    simplexFace 0 (conedTriangleSubsimplex (stellarConeMap omitted) simplex) =
      stellarSubsimplex omitted simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [conedTriangleSubsimplex, stellarSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, coneOverTriangleMap_face_zero_stellar]

theorem conedTriangleSubsimplex_face_zero_id (simplex : SphereSingularSimplex 2) :
    simplexFace 0 (conedTriangleSubsimplex (ContinuousMap.id Triangle) simplex) =
      simplex := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [conedTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, coneOverTriangleMap_face_zero_id]
  simp

theorem conedTriangleSubsimplex_face_eq_of_map_eq
    (left right : C(Triangle, Triangle)) (leftFace rightFace : Fin 4)
    (hface : (coneOverTriangleMap left).comp
        (simplexFaceMap (degree := 2) leftFace) =
      (coneOverTriangleMap right).comp
        (simplexFaceMap (degree := 2) rightFace))
    (simplex : SphereSingularSimplex 2) :
    simplexFace leftFace (conedTriangleSubsimplex left simplex) =
      simplexFace rightFace (conedTriangleSubsimplex right simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [conedTriangleSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, hface]

theorem conedTriangleSubsimplex_spoke_02 (simplex : SphereSingularSimplex 2) :
    simplexFace 2 (conedTriangleSubsimplex (stellarConeMap 0) simplex) =
      simplexFace 2 (conedTriangleSubsimplex (stellarConeMap 1) simplex) :=
  conedTriangleSubsimplex_face_eq_of_map_eq _ _ 2 2
    coneOverTriangleMap_spoke_02 simplex

theorem conedTriangleSubsimplex_spoke_01 (simplex : SphereSingularSimplex 2) :
    simplexFace 3 (conedTriangleSubsimplex (stellarConeMap 0) simplex) =
      simplexFace 2 (conedTriangleSubsimplex (stellarConeMap 2) simplex) :=
  conedTriangleSubsimplex_face_eq_of_map_eq _ _ 3 2
    coneOverTriangleMap_spoke_01 simplex

theorem conedTriangleSubsimplex_spoke_00 (simplex : SphereSingularSimplex 2) :
    simplexFace 3 (conedTriangleSubsimplex (stellarConeMap 1) simplex) =
      simplexFace 3 (conedTriangleSubsimplex (stellarConeMap 2) simplex) :=
  conedTriangleSubsimplex_face_eq_of_map_eq _ _ 3 3
    coneOverTriangleMap_spoke_00 simplex

theorem conedTriangleSubsimplex_exterior_zero (omitted : Fin 3)
    (simplex : SphereSingularSimplex 2) :
    simplexFace 1 (conedTriangleSubsimplex (stellarConeMap omitted) simplex) =
      simplexFace omitted.succ
        (conedTriangleSubsimplex (ContinuousMap.id Triangle) simplex) :=
  conedTriangleSubsimplex_face_eq_of_map_eq _ _ 1 omitted.succ
    (coneOverTriangleMap_exterior_zero omitted) simplex

/-- The exact cone on `stellarSubdivision simplex - simplexGenerator simplex`. -/
def stellarSubdivisionHomotopy (simplex : SphereSingularSimplex 2) : SphereChain 3 :=
  (∑ omitted : Fin 3, (-1 : ℚ) ^ (omitted : ℕ) •
    simplexGenerator
      (conedTriangleSubsimplex (stellarConeMap omitted) simplex)) -
    simplexGenerator
      (conedTriangleSubsimplex (ContinuousMap.id Triangle) simplex)

/-- The homotopy boundary is exactly subdivision minus identity; all six coned edge seams cancel. -/
theorem boundary_stellarSubdivisionHomotopy (simplex : SphereSingularSimplex 2) :
    SphereSingularChainComplex.d 3 2 (stellarSubdivisionHomotopy simplex) =
      stellarSubdivision simplex - simplexGenerator simplex := by
  rw [stellarSubdivisionHomotopy, map_sub, map_sum]
  simp only [map_smul, boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_four]
  rw [conedTriangleSubsimplex_face_zero_stellar 0,
    conedTriangleSubsimplex_face_zero_stellar 1,
    conedTriangleSubsimplex_face_zero_stellar 2,
    conedTriangleSubsimplex_face_zero_id]
  rw [conedTriangleSubsimplex_spoke_02,
    conedTriangleSubsimplex_spoke_01,
    conedTriangleSubsimplex_spoke_00,
    conedTriangleSubsimplex_exterior_zero 0,
    conedTriangleSubsimplex_exterior_zero 1,
    conedTriangleSubsimplex_exterior_zero 2]
  rw [stellarSubdivision]
  repeat rw [Fin.sum_univ_three]
  simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide]
  norm_num
  module

/-- Coefficient transport into the explicit homotopy of one singular triangle. -/
def stellarSubdivisionHomotopyCoefficient (value : SphereChain 3) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 3 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • value
      map_add' := fun left right => add_smul left right value
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
        rfl }

/-- Coproduct-linear extension of the barycentric cone homotopy to every singular two-chain. -/
def stellarSubdivisionHomotopyMorphism :
    SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 3 :=
  Limits.Sigma.desc fun simplex =>
    stellarSubdivisionHomotopyCoefficient (stellarSubdivisionHomotopy simplex)

@[simp]
theorem stellarSubdivisionHomotopyMorphism_simplexGenerator
    (simplex : SphereSingularSimplex 2) :
    stellarSubdivisionHomotopyMorphism (simplexGenerator simplex) =
      stellarSubdivisionHomotopy simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source =>
          stellarSubdivisionHomotopyCoefficient
            (stellarSubdivisionHomotopy source))) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- Chain-homotopy identity: coning the returned difference reconstructs subdivision minus the
identity on every addressed two-chain. -/
theorem boundary_stellarSubdivisionHomotopyMorphism (chain : SphereChain 2) :
    SphereSingularChainComplex.d 3 2
        (stellarSubdivisionHomotopyMorphism chain) =
      stellarSubdivisionMorphism chain - chain := by
  let left : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 2 :=
    stellarSubdivisionHomotopyMorphism ≫ SphereSingularChainComplex.d 3 2
  let right : SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 2 :=
    stellarSubdivisionMorphism - 𝟙 _
  have hleftRight : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change ℚ at coefficient
    simp only [left, right]
    change SphereSingularChainComplex.d 3 2
        (stellarSubdivisionHomotopyMorphism
          ((Limits.Sigma.ι
            (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex) coefficient)) =
      ((stellarSubdivisionMorphism - 𝟙 _) :
        SphereSingularChainComplex.X 2 ⟶ SphereSingularChainComplex.X 2)
        ((Limits.Sigma.ι
          (fun _ : SphereSingularSimplex 2 => rationalCoefficient) simplex) coefficient)
    rw [HodgeTetrahedralCarrierAssembly.sigmaInjection_eq_smul_simplexGenerator]
    change SphereSingularChainComplex.d 3 2
        (stellarSubdivisionHomotopyMorphism
          (coefficient • simplexGenerator simplex)) =
      stellarSubdivisionMorphism (coefficient • simplexGenerator simplex) -
        coefficient • simplexGenerator simplex
    simp only [map_smul, stellarSubdivisionHomotopyMorphism_simplexGenerator,
      boundary_stellarSubdivisionHomotopy,
      stellarSubdivisionMorphism_simplexGenerator]
    exact smul_sub (M := ℚ) (A := SphereChain 2) coefficient
      (stellarSubdivision simplex) (simplexGenerator simplex)
  exact congrArg (fun morphism => morphism chain) hleftRight

theorem stellarSubdivisionHomotopyMorphism_comp_boundary :
    stellarSubdivisionHomotopyMorphism ≫ SphereSingularChainComplex.d 3 2 =
      stellarSubdivisionMorphism - 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro chain
  exact boundary_stellarSubdivisionHomotopyMorphism chain

/-- Correct the basic tetrahedral refinement by coning the already-refined boundary.  The basic
four-cone term retains the source tetrahedron's exterior; the second term contributes precisely
the difference between the refined and unrefined exterior. -/
def recursiveStellarSubdivisionMorphism :
    SphereSingularChainComplex.X 3 ⟶ SphereSingularChainComplex.X 3 :=
  tetrahedralStellarSubdivisionMorphism +
    SphereSingularChainComplex.d 3 2 ≫ stellarSubdivisionHomotopyMorphism

/-- The corrected degree-three current and the checked degree-two current form an exact chain-map
square.  This removes `recursiveSubdivisionDefect` rather than assuming it vanishes. -/
theorem recursiveStellarSubdivisionMorphism_comp_boundary :
    recursiveStellarSubdivisionMorphism ≫ SphereSingularChainComplex.d 3 2 =
      SphereSingularChainComplex.d 3 2 ≫ stellarSubdivisionMorphism := by
  rw [recursiveStellarSubdivisionMorphism, Preadditive.add_comp,
    tetrahedralStellarSubdivisionMorphism_comp_boundary, Category.assoc,
    stellarSubdivisionHomotopyMorphism_comp_boundary,
    Preadditive.comp_sub, Category.comp_id]
  module

theorem boundary_recursiveStellarSubdivisionMorphism (chain : SphereChain 3) :
    SphereSingularChainComplex.d 3 2
        (recursiveStellarSubdivisionMorphism chain) =
      stellarSubdivisionMorphism (SphereSingularChainComplex.d 3 2 chain) := by
  simpa only [ConcreteCategory.comp_apply] using
    congrArg (fun morphism : SphereSingularChainComplex.X 3 ⟶
      SphereSingularChainComplex.X 2 => morphism chain)
      recursiveStellarSubdivisionMorphism_comp_boundary

/-- Synchronized iteration of the corrected degree-three refinement. -/
def iteratedRecursiveStellarSubdivision : ℕ → SphereChain 3 → SphereChain 3
  | 0 => id
  | scale + 1 => fun chain =>
      recursiveStellarSubdivisionMorphism
        (iteratedRecursiveStellarSubdivision scale chain)

/-- Uniform recursive-scale theorem: after every finite number of refinements, the complete
degree-three boundary is exactly the equally refined degree-two current. -/
theorem boundary_iteratedRecursiveStellarSubdivision (scale : ℕ) (chain : SphereChain 3) :
    SphereSingularChainComplex.d 3 2
        (iteratedRecursiveStellarSubdivision scale chain) =
      iteratedStellarSubdivision scale
        (SphereSingularChainComplex.d 3 2 chain) := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      rw [iteratedRecursiveStellarSubdivision,
        boundary_recursiveStellarSubdivisionMorphism,
        iteratedStellarSubdivision, inductionHypothesis]

section Audit

#print axioms coneOverTriangleMap_face_succ
#print axioms boundary_stellarSubdivisionHomotopy
#print axioms stellarSubdivisionHomotopyMorphism_comp_boundary
#print axioms recursiveStellarSubdivisionMorphism_comp_boundary
#print axioms boundary_iteratedRecursiveStellarSubdivision

end Audit

end Soma.Holonics.Millennium.HodgeStellarSubdivisionHomotopy
