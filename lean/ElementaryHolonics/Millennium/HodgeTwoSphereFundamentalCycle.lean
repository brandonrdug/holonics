import ElementaryHolonics.Millennium.HodgeProjectiveLineTopology
import ElementaryHolonics.Millennium.HodgeProjectiveLineSingularReduction
import Mathlib.Analysis.Normed.Module.Normalize

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle

open Set

abbrev Triangle := stdSimplex ℝ (Fin 3)
abbrev Tetrahedron := stdSimplex ℝ (Fin 4)
abbrev AmbientThree := EuclideanSpace ℝ (Fin 3)
abbrev TwoSphere := Metric.sphere (0 : AmbientThree) 1

def tetraFace (face : Fin 4) : Triangle → Tetrahedron :=
  stdSimplex.map face.succAbove

theorem tetraFace_continuous (face : Fin 4) : Continuous (tetraFace face) :=
  stdSimplex.continuous_map face.succAbove

theorem tetraFace_missing_coordinate (face : Fin 4) (point : Triangle) :
    tetraFace face point face = 0 := by
  change FunOnFinite.linearMap ℝ ℝ face.succAbove point face = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove_ne]

def centeredFaceVector (face : Fin 4) (point : Triangle) : AmbientThree :=
  WithLp.toLp 2 (fun i : Fin 3 => tetraFace face point i.castSucc - (1 / 4 : ℝ))

theorem centeredFaceVector_apply (face : Fin 4) (point : Triangle) (i : Fin 3) :
    centeredFaceVector face point i = tetraFace face point i.castSucc - (1 / 4 : ℝ) := rfl

theorem centeredFaceVector_continuous (face : Fin 4) :
    Continuous (centeredFaceVector face) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    ((continuous_apply i.castSucc).comp
      (continuous_subtype_val.comp (tetraFace_continuous face))).sub continuous_const)

theorem centeredFaceVector_ne_zero (face : Fin 4) (point : Triangle) :
    centeredFaceVector face point ≠ 0 := by
  intro hzero
  have hcoordinate (i : Fin 3) : tetraFace face point i.castSucc = (1 / 4 : ℝ) := by
    have := congrFun (congrArg WithLp.ofLp hzero) i
    exact sub_eq_zero.mp (by simpa [centeredFaceVector] using this)
  have hthree : tetraFace face point (3 : Fin 4) = (1 / 4 : ℝ) := by
    have hsum := stdSimplex.sum_eq_one (tetraFace face point)
    rw [Fin.sum_univ_four] at hsum
    have h0 : tetraFace face point (0 : Fin 4) = (1 / 4 : ℝ) := by
      simpa using hcoordinate 0
    have h1 : tetraFace face point (1 : Fin 4) = (1 / 4 : ℝ) := by
      simpa using hcoordinate 1
    have h2 : tetraFace face point (2 : Fin 4) = (1 / 4 : ℝ) := by
      simpa using hcoordinate 2
    linarith [hsum, h0, h1, h2]
  have hall (i : Fin 4) : tetraFace face point i = (1 / 4 : ℝ) := by
    fin_cases i
    · simpa using hcoordinate 0
    · simpa using hcoordinate 1
    · simpa using hcoordinate 2
    · simpa using hthree
  have := tetraFace_missing_coordinate face point
  rw [hall face] at this
  norm_num at this

def radialFace (face : Fin 4) : C(Triangle, TwoSphere) where
  toFun point := ⟨NormedSpace.normalize (centeredFaceVector face point),
    mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize (centeredFaceVector_ne_zero face point))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [show (fun point : Triangle => NormedSpace.normalize (centeredFaceVector face point)) =
      fun point => ‖centeredFaceVector face point‖⁻¹ • centeredFaceVector face point by rfl]
    exact (centeredFaceVector_continuous face).norm.inv₀
      (fun point hnorm => centeredFaceVector_ne_zero face point (norm_eq_zero.mp hnorm)) |>.smul
      (centeredFaceVector_continuous face)

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction

def sphereTopCat : TopCat := TopCat.of TwoSphere

abbrev SphereSingularSimplex (degree : ℕ) :=
  (TopCat.toSSet.obj sphereTopCat).obj (Opposite.op (SimplexCategory.mk degree))

def radialSingularSimplex (face : Fin 4) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm (radialFace face)

abbrev SphereSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).obj sphereTopCat

abbrev SphereSimplicialModule : SimplicialObject (ModuleCat ℚ) :=
  ((SimplicialObject.whiskering Type (ModuleCat ℚ)).obj
    (sigmaConst.obj rationalCoefficient)).obj (TopCat.toSSet.obj sphereTopCat)

example : SphereSingularChainComplex =
    AlgebraicTopology.AlternatingFaceMapComplex.obj SphereSimplicialModule := rfl

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

abbrev simplexGenerator {degree : ℕ} (simplex : SphereSingularSimplex degree) :
    SphereChain degree := by
  change ↑((sigmaConst.obj rationalCoefficient).obj (SphereSingularSimplex degree))
  exact (Limits.Sigma.ι (fun _ : SphereSingularSimplex degree => rationalCoefficient) simplex) (1 : ℚ)

def sphereFundamentalCandidate : SphereChain 2 :=
  ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) • simplexGenerator (radialSingularSimplex face)

def simplexFace {degree : ℕ} (i : Fin (degree + 2))
    (simplex : SphereSingularSimplex (degree + 1)) : SphereSingularSimplex degree :=
  (TopCat.toSSet.obj sphereTopCat).δ i simplex

def simplexFaceMap {degree : ℕ} (i : Fin (degree + 2)) :
    C(stdSimplex ℝ (Fin (degree + 1)), stdSimplex ℝ (Fin (degree + 2))) where
  toFun := stdSimplex.map (SimplexCategory.δ i).toOrderHom
  continuous_toFun := stdSimplex.continuous_map _

theorem simplexFace_realization {degree : ℕ} (i : Fin (degree + 2))
    (simplex : SphereSingularSimplex (degree + 1)) :
    TopCat.toSSetObjEquiv sphereTopCat (Opposite.op (SimplexCategory.mk degree))
        (simplexFace i simplex) =
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk (degree + 1))) simplex).comp
          (simplexFaceMap i) := by
  rfl

theorem simplicialModule_face_generator {degree : ℕ} (i : Fin (degree + 2))
    (simplex : SphereSingularSimplex (degree + 1)) :
    (SphereSimplicialModule.δ i) (simplexGenerator simplex) =
      simplexGenerator (simplexFace i simplex) := by
  change (ModuleCat.Hom.hom (Limits.Sigma.map'
      (f := fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient)
      (g := fun _ : SphereSingularSimplex degree => rationalCoefficient)
      ((TopCat.toSSet.obj sphereTopCat).δ i)
      (fun _ => 𝟙 rationalCoefficient)))
      ((ModuleCat.Hom.hom
        (Limits.Sigma.ι (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient)
          simplex)) (1 : ℚ)) = _
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient) simplex ≫
      Limits.Sigma.map'
        (f := fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient)
        (g := fun _ : SphereSingularSimplex degree => rationalCoefficient)
        ((TopCat.toSSet.obj sphereTopCat).δ i)
        (fun _ => 𝟙 rationalCoefficient)) (1 : ℚ)) = _
  simp [simplexGenerator, simplexFace]
  rfl

theorem boundary_simplexGenerator {degree : ℕ}
    (simplex : SphereSingularSimplex (degree + 1)) :
    (SphereSingularChainComplex.d (degree + 1) degree)
        (simplexGenerator simplex) =
      ∑ i : Fin (degree + 2), (-1 : ℚ) ^ (i : ℕ) •
        simplexGenerator (simplexFace i simplex) := by
  dsimp only [SphereSingularChainComplex, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor, Functor.comp_obj]
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj SphereSimplicialModule).d
    (degree + 1) degree) (simplexGenerator simplex) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply,
    ModuleCat.hom_zsmul]
  have hsum :
      ((∑ i : Fin (degree + 2),
          ⇑(((-1 : ℤ) ^ (i : ℕ)) • ModuleCat.Hom.hom (SphereSimplicialModule.δ i)))
          (simplexGenerator simplex)) =
        ∑ i : Fin (degree + 2),
          (⇑(((-1 : ℤ) ^ (i : ℕ)) • ModuleCat.Hom.hom (SphereSimplicialModule.δ i)))
            (simplexGenerator simplex) := by
    simpa only [LinearMap.coe_sum] using
      (LinearMap.sum_apply (Finset.univ : Finset (Fin (degree + 2)))
      (fun i => ((-1 : ℤ) ^ (i : ℕ)) • ModuleCat.Hom.hom (SphereSimplicialModule.δ i))
      (simplexGenerator simplex))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  change ((-1 : ℤ) ^ (i : ℕ)) •
      (SphereSimplicialModule.δ i) (simplexGenerator simplex) =
    ((-1 : ℚ) ^ (i : ℕ)) • simplexGenerator (simplexFace i simplex)
  rw [simplicialModule_face_generator]
  have hscalar : ((-1 : ℚ) ^ (i : ℕ)) = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : ℚ) := by
    norm_num
  rw [hscalar, Int.cast_smul_eq_zsmul]
  rfl

theorem radialFace_face_eq_of_composite_eq
    (firstFace secondFace : Fin 4) (firstLocal secondLocal : Fin 3)
    (hcomposite : firstFace.succAbove ∘ firstLocal.succAbove =
      secondFace.succAbove ∘ secondLocal.succAbove) :
    (radialFace firstFace).comp (simplexFaceMap (degree := 1) firstLocal) =
      (radialFace secondFace).comp (simplexFaceMap (degree := 1) secondLocal) := by
  apply ContinuousMap.ext
  intro point
  apply Subtype.ext
  change NormedSpace.normalize
      (centeredFaceVector firstFace
        (stdSimplex.map (SimplexCategory.δ firstLocal).toOrderHom point)) =
    NormedSpace.normalize
      (centeredFaceVector secondFace
        (stdSimplex.map (SimplexCategory.δ secondLocal).toOrderHom point))
  congr 1
  unfold centeredFaceVector tetraFace
  simp only [SimplexCategory.δ]
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have hcomposite' : firstFace.succAbove ∘
        ⇑(SimplexCategory.Hom.toOrderHom
          (SimplexCategory.mkHom firstLocal.succAboveOrderEmb.toOrderHom)) =
      secondFace.succAbove ∘
        ⇑(SimplexCategory.Hom.toOrderHom
          (SimplexCategory.mkHom secondLocal.succAboveOrderEmb.toOrderHom)) := by
    funext i
    have hi := congrFun hcomposite i
    simpa [Function.comp_apply, Fin.succAboveOrderEmb_apply] using hi
  rw [hcomposite']

theorem radialFace_face_00 :
    (radialFace 0).comp (simplexFaceMap (degree := 1) 0) =
      (radialFace 1).comp (simplexFaceMap (degree := 1) 0) := by
  apply radialFace_face_eq_of_composite_eq
  funext i
  fin_cases i <;> rfl

theorem radialSingularSimplex_face_eq_of_composite_eq
    (firstFace secondFace : Fin 4) (firstLocal secondLocal : Fin 3)
    (hcomposite : firstFace.succAbove ∘ firstLocal.succAbove =
      secondFace.succAbove ∘ secondLocal.succAbove) :
    simplexFace firstLocal (radialSingularSimplex firstFace) =
      simplexFace secondLocal (radialSingularSimplex secondFace) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization, simplexFace_realization]
  simp only [radialSingularSimplex, Equiv.apply_symm_apply]
  exact radialFace_face_eq_of_composite_eq _ _ _ _ hcomposite

theorem radialSingularSimplex_edge_23 :
    simplexFace 0 (radialSingularSimplex 0) =
      simplexFace 0 (radialSingularSimplex 1) := by
  apply radialSingularSimplex_face_eq_of_composite_eq
  funext i
  fin_cases i <;> rfl

theorem radialSingularSimplex_edge_13 :
    simplexFace 1 (radialSingularSimplex 0) =
      simplexFace 0 (radialSingularSimplex 2) := by
  apply radialSingularSimplex_face_eq_of_composite_eq
  funext i
  fin_cases i <;> rfl

theorem radialSingularSimplex_edge_12 :
    simplexFace 2 (radialSingularSimplex 0) =
      simplexFace 0 (radialSingularSimplex 3) := by
  apply radialSingularSimplex_face_eq_of_composite_eq
  funext i
  fin_cases i <;> rfl

theorem radialSingularSimplex_edge_03 :
    simplexFace 1 (radialSingularSimplex 1) =
      simplexFace 1 (radialSingularSimplex 2) := by
  apply radialSingularSimplex_face_eq_of_composite_eq
  funext i
  fin_cases i <;> rfl

theorem radialSingularSimplex_edge_02 :
    simplexFace 2 (radialSingularSimplex 1) =
      simplexFace 1 (radialSingularSimplex 3) := by
  apply radialSingularSimplex_face_eq_of_composite_eq
  funext i
  fin_cases i <;> rfl

theorem radialSingularSimplex_edge_01 :
    simplexFace 2 (radialSingularSimplex 2) =
      simplexFace 2 (radialSingularSimplex 3) := by
  apply radialSingularSimplex_face_eq_of_composite_eq
  funext i
  fin_cases i <;> rfl

theorem boundary_radialSingularSimplex (face : Fin 4) :
    (SphereSingularChainComplex.d 2 1)
        (simplexGenerator (radialSingularSimplex face)) =
      simplexGenerator (simplexFace 0 (radialSingularSimplex face)) -
        simplexGenerator (simplexFace 1 (radialSingularSimplex face)) +
          simplexGenerator (simplexFace 2 (radialSingularSimplex face)) := by
  rw [boundary_simplexGenerator]
  rw [Fin.sum_univ_three]
  norm_num
  simp only [sub_eq_add_neg]

/-- The tetrahedral boundary candidate is an actual rational singular two-cycle. -/
theorem sphereFundamentalCandidate_boundary_zero :
    (SphereSingularChainComplex.d 2 1) sphereFundamentalCandidate = 0 := by
  rw [sphereFundamentalCandidate]
  simp only [map_sum, map_smul]
  rw [Fin.sum_univ_four]
  rw [boundary_radialSingularSimplex, boundary_radialSingularSimplex,
    boundary_radialSingularSimplex, boundary_radialSingularSimplex]
  norm_num
  rw [radialSingularSimplex_edge_23, radialSingularSimplex_edge_13,
    radialSingularSimplex_edge_12, radialSingularSimplex_edge_03,
    radialSingularSimplex_edge_02, radialSingularSimplex_edge_01]
  abel

section Audit

#print axioms radialFace
#print axioms simplexFace_realization
#print axioms boundary_simplexGenerator
#print axioms radialSingularSimplex_face_eq_of_composite_eq
#print axioms sphereFundamentalCandidate_boundary_zero

end Audit

end Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
