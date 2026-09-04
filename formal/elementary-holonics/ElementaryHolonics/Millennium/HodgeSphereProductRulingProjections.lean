import ElementaryHolonics.Millennium.HodgeSphereProductRulingHomology
import ElementaryHolonics.Millennium.HodgeTetrahedralSphereComplex

/-!
# Projection receivers for the two geometric ruling classes

Both ruling inclusions admit their geometric coordinate projections as exact retractions.  At the
singular-chain level the matching projection returns the tetrahedral sphere cycle, while the
crossed projection is literally zero: all four faces become one constant simplex and their
alternating coefficients cancel.

These identities descend through the categorical cycle and homology quotients.  Consequently the
two ruling classes are linearly independent as soon as the explicitly constructed sphere class is
proved nonzero.  This isolates the next construction to one source-specific fact about that class;
it does not appeal to or wait for a packaged sphere-homology computation.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereProductRulingProjections

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeSphereProductRulingCycles
open Soma.Holonics.Millennium.HodgeSphereProductRulingHomology
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex

def firstProjectionContinuousMap : C(Sphere × Sphere, Sphere) where
  toFun point := point.1
  continuous_toFun := continuous_fst

def secondProjectionContinuousMap : C(Sphere × Sphere, Sphere) where
  toFun point := point.2
  continuous_toFun := continuous_snd

def firstProjectionTopMap : sphereProductTopCat ⟶ sphereTopCat :=
  TopCat.ofHom firstProjectionContinuousMap

def secondProjectionTopMap : sphereProductTopCat ⟶ sphereTopCat :=
  TopCat.ofHom secondProjectionContinuousMap

def firstProjectionChainMap :
    SphereProductSingularChainComplex ⟶ SphereSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map firstProjectionTopMap

def secondProjectionChainMap :
    SphereProductSingularChainComplex ⟶ SphereSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map secondProjectionTopMap

theorem first_ruling_then_first_projection :
    firstRulingTopMap ≫ firstProjectionTopMap = 𝟙 sphereTopCat := by
  ext point
  rfl

theorem second_ruling_then_second_projection :
    secondRulingTopMap ≫ secondProjectionTopMap = 𝟙 sphereTopCat := by
  ext point
  rfl

theorem firstRulingChainMap_retract :
    firstRulingChainMap ≫ firstProjectionChainMap = 𝟙 SphereSingularChainComplex := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map firstRulingTopMap ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map firstProjectionTopMap = _
  rw [← Functor.map_comp, first_ruling_then_first_projection]
  simp

theorem secondRulingChainMap_retract :
    secondRulingChainMap ≫ secondProjectionChainMap = 𝟙 SphereSingularChainComplex := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map secondRulingTopMap ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map secondProjectionTopMap = _
  rw [← Functor.map_comp, second_ruling_then_second_projection]
  simp

def constantSphereContinuousMap : C(Sphere, Sphere) where
  toFun _ := sphereBasepoint
  continuous_toFun := continuous_const

def constantSphereTopMap : sphereTopCat ⟶ sphereTopCat :=
  TopCat.ofHom constantSphereContinuousMap

def constantSphereChainMap : SphereSingularChainComplex ⟶ SphereSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map constantSphereTopMap

abbrev SphereSimplex (degree : ℕ) :=
  (TopCat.toSSet.obj sphereTopCat).obj (Opposite.op (SimplexCategory.mk degree))

def sphereSimplexMap {degree : ℕ} (map : sphereTopCat ⟶ sphereTopCat)
    (simplex : SphereSimplex degree) : SphereSimplex degree :=
  (TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)) simplex

theorem sphereChainMap_simplexGenerator {degree : ℕ}
    (map : sphereTopCat ⟶ sphereTopCat) (simplex : SphereSimplex degree) :
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map map).f degree (simplexGenerator simplex) =
      simplexGenerator (sphereSimplexMap map simplex) := by
  change (ModuleCat.Hom.hom (Limits.Sigma.map'
      (f := fun _ : SphereSimplex degree => rationalCoefficient)
      (g := fun _ : SphereSimplex degree => rationalCoefficient)
      ((TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)))
      (fun _ => 𝟙 rationalCoefficient)))
      ((ModuleCat.Hom.hom
        (Limits.Sigma.ι (fun _ : SphereSimplex degree => rationalCoefficient)
          simplex)) (1 : ℚ)) = _
  have hinclusion := Limits.Sigma.ι_comp_map'
      (f := fun _ : SphereSimplex degree => rationalCoefficient)
      (g := fun _ : SphereSimplex degree => rationalCoefficient)
      ((TopCat.toSSet.map map).app (Opposite.op (SimplexCategory.mk degree)))
      (fun _ : SphereSimplex degree => 𝟙 rationalCoefficient) simplex
  let one : (rationalCoefficient : Type) := (1 : ℚ)
  have hevaluated := congrArg
      (fun morphism =>
        (ModuleCat.Hom.hom morphism) one)
      hinclusion
  exact hevaluated

def constantSphereSimplex (degree : ℕ) : SphereSimplex degree :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk degree))).symm
      ⟨fun _ => sphereBasepoint, continuous_const⟩

theorem constantSphereMap_radialSimplex (face : Fin 4) :
    sphereSimplexMap constantSphereTopMap (radialSingularSimplex face) =
      constantSphereSimplex 2 := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  apply ContinuousMap.ext
  intro point
  rfl

theorem second_ruling_then_first_projection :
    secondRulingTopMap ≫ firstProjectionTopMap = constantSphereTopMap := by
  ext point
  rfl

theorem first_ruling_then_second_projection :
    firstRulingTopMap ≫ secondProjectionTopMap = constantSphereTopMap := by
  ext point
  rfl

theorem secondRuling_firstProjection_chainMap :
    secondRulingChainMap ≫ firstProjectionChainMap = constantSphereChainMap := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map secondRulingTopMap ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map firstProjectionTopMap = _
  rw [← Functor.map_comp, second_ruling_then_first_projection]
  rfl

theorem firstRuling_secondProjection_chainMap :
    firstRulingChainMap ≫ secondProjectionChainMap = constantSphereChainMap := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map firstRulingTopMap ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map secondProjectionTopMap = _
  rw [← Functor.map_comp, first_ruling_then_second_projection]
  rfl

theorem constantSphereChainMap_fundamentalCandidate_zero :
    constantSphereChainMap.f 2 sphereFundamentalCandidate = 0 := by
  rw [sphereFundamentalCandidate, map_sum]
  simp_rw [map_smul]
  simp_rw [constantSphereChainMap, sphereChainMap_simplexGenerator,
    constantSphereMap_radialSimplex]
  rw [Fin.sum_univ_four]
  norm_num

theorem first_projection_first_ruling_cycle :
    firstProjectionChainMap.f 2 firstRulingCycle = sphereFundamentalCandidate := by
  change (firstRulingChainMap ≫ firstProjectionChainMap).f 2
    sphereFundamentalCandidate = sphereFundamentalCandidate
  rw [firstRulingChainMap_retract]
  rfl

theorem second_projection_second_ruling_cycle :
    secondProjectionChainMap.f 2 secondRulingCycle = sphereFundamentalCandidate := by
  change (secondRulingChainMap ≫ secondProjectionChainMap).f 2
    sphereFundamentalCandidate = sphereFundamentalCandidate
  rw [secondRulingChainMap_retract]
  rfl

theorem first_projection_second_ruling_cycle :
    firstProjectionChainMap.f 2 secondRulingCycle = 0 := by
  change (secondRulingChainMap ≫ firstProjectionChainMap).f 2
    sphereFundamentalCandidate = 0
  rw [secondRuling_firstProjection_chainMap]
  exact constantSphereChainMap_fundamentalCandidate_zero

theorem second_projection_first_ruling_cycle :
    secondProjectionChainMap.f 2 firstRulingCycle = 0 := by
  change (firstRulingChainMap ≫ secondProjectionChainMap).f 2
    sphereFundamentalCandidate = 0
  rw [firstRuling_secondProjection_chainMap]
  exact constantSphereChainMap_fundamentalCandidate_zero

abbrev SphereScalarModule := ModuleCat.of ℚ ℚ

def sphereCycleMorphism : SphereScalarModule ⟶ SphereSingularChainComplex.X 2 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ sphereFundamentalCandidate)

theorem sphereCycleMorphism_comp_boundary_eq_zero :
    sphereCycleMorphism ≫ SphereSingularChainComplex.d 2 1 = 0 := by
  ext
  change SphereSingularChainComplex.d 2 1
    ((1 : ℚ) • sphereFundamentalCandidate) = 0
  simpa using sphereFundamentalCandidate_boundary_zero

def sphereCycleLift : SphereScalarModule ⟶ SphereSingularChainComplex.cycles 2 :=
  SphereSingularChainComplex.liftCycles sphereCycleMorphism 1 (by simp)
    sphereCycleMorphism_comp_boundary_eq_zero

theorem sphereCycleLift_i :
    sphereCycleLift ≫ SphereSingularChainComplex.iCycles 2 =
      sphereCycleMorphism := by
  apply HomologicalComplex.liftCycles_i

def sphereFundamentalHomologyMorphism :
    SphereScalarModule ⟶ RationalSingularHomology 2 sphereTopCat :=
  sphereCycleLift ≫ SphereSingularChainComplex.homologyπ 2

def sphereFundamentalHomologyClass : RationalSingularHomology 2 sphereTopCat :=
  sphereFundamentalHomologyMorphism 1

theorem tetrahedralCycleLift_fundamental_eq_sphereCycleLift :
    tetrahedralCycleLift fundamentalClass = sphereCycleLift 1 := by
  apply (ModuleCat.mono_iff_injective (SphereSingularChainComplex.iCycles 2)).mp
    inferInstance
  change (tetrahedralCycleLift ≫ SphereSingularChainComplex.iCycles 2)
      fundamentalClass =
    (sphereCycleLift ≫ SphereSingularChainComplex.iCycles 2) 1
  rw [tetrahedralCycleLift_i, sphereCycleLift_i]
  rw [tetrahedralCycleMorphism_fundamental]
  exact (LinearMap.toSpanSingleton_apply_one ℚ _ sphereFundamentalCandidate).symm

theorem realizedFundamentalClass_eq_sphereFundamentalHomologyClass :
    realizedFundamentalClass = sphereFundamentalHomologyClass := by
  change (SphereSingularChainComplex.homologyπ 2)
      (tetrahedralCycleLift fundamentalClass) =
    (SphereSingularChainComplex.homologyπ 2) (sphereCycleLift 1)
  rw [tetrahedralCycleLift_fundamental_eq_sphereCycleLift]

abbrev SingularRealizationObstruction :=
  LinearMap.ker tetrahedralHomologyRealization.hom

theorem tetrahedralHomologyRealization_injective_iff :
    Function.Injective tetrahedralHomologyRealization ↔
      sphereFundamentalHomologyClass ≠ 0 := by
  constructor
  · intro hinjective hzero
    have hmap : tetrahedralHomologyRealization fundamentalClass =
        tetrahedralHomologyRealization 0 := by
      rw [map_zero]
      change realizedFundamentalClass = 0
      rw [realizedFundamentalClass_eq_sphereFundamentalHomologyClass, hzero]
      rfl
    exact fundamentalClass_ne_zero (hinjective hmap)
  · intro hnonzero x y hxy
    have hdifference : tetrahedralHomologyRealization (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hcoordinates : x - y = (x - y).1 0 • fundamentalClass := by
      apply Subtype.ext
      exact cycle_coordinates (x - y).1 (x - y).2
    have hcoefficientImage :
        (x - y).1 0 • sphereFundamentalHomologyClass = 0 := by
      rw [← realizedFundamentalClass_eq_sphereFundamentalHomologyClass]
      have hmapped := congrArg
        (fun z : (tetrahedralH2Module : Type) => tetrahedralHomologyRealization z)
        hcoordinates
      have hmapped' :
          tetrahedralHomologyRealization (x - y) =
            (x - y).1 0 • tetrahedralHomologyRealization fundamentalClass := by
        exact hmapped.trans
          (map_smul tetrahedralHomologyRealization.hom ((x - y).1 0) fundamentalClass)
      exact hmapped'.symm.trans hdifference
    have hcoefficient : (x - y).1 0 = 0 :=
      (smul_eq_zero.mp hcoefficientImage).resolve_right hnonzero
    apply sub_eq_zero.mp
    rw [hcoordinates, hcoefficient, zero_smul]
    rfl

theorem fundamentalClass_mem_obstruction_iff :
    fundamentalClass ∈ SingularRealizationObstruction ↔
      sphereFundamentalHomologyClass = 0 := by
  change tetrahedralHomologyRealization fundamentalClass = 0 ↔ _
  exact realizedFundamentalClass_eq_sphereFundamentalHomologyClass.congr_left

def firstProjectionHomologyMap :
    RationalSingularHomology 2 sphereProductTopCat ⟶
      RationalSingularHomology 2 sphereTopCat :=
  HomologicalComplex.homologyMap firstProjectionChainMap 2

def secondProjectionHomologyMap :
    RationalSingularHomology 2 sphereProductTopCat ⟶
      RationalSingularHomology 2 sphereTopCat :=
  HomologicalComplex.homologyMap secondProjectionChainMap 2

theorem firstRuling_cyclesMap_eq_sphereCycleLift :
    cycleLift firstRulingCycle firstRulingCycle_boundary_zero ≫
        HomologicalComplex.cyclesMap firstProjectionChainMap 2 =
      sphereCycleLift := by
  apply (cancel_mono (SphereSingularChainComplex.iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, cycleLift_i, sphereCycleLift_i]
  ext
  change firstProjectionChainMap.f 2 ((1 : ℚ) • firstRulingCycle) =
    (1 : ℚ) • sphereFundamentalCandidate
  simpa using first_projection_first_ruling_cycle

theorem secondRuling_cyclesMap_eq_sphereCycleLift :
    cycleLift secondRulingCycle secondRulingCycle_boundary_zero ≫
        HomologicalComplex.cyclesMap secondProjectionChainMap 2 =
      sphereCycleLift := by
  apply (cancel_mono (SphereSingularChainComplex.iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, cycleLift_i, sphereCycleLift_i]
  ext
  change secondProjectionChainMap.f 2 ((1 : ℚ) • secondRulingCycle) =
    (1 : ℚ) • sphereFundamentalCandidate
  simpa using second_projection_second_ruling_cycle

theorem secondRuling_firstProjection_cyclesMap_zero :
    cycleLift secondRulingCycle secondRulingCycle_boundary_zero ≫
        HomologicalComplex.cyclesMap firstProjectionChainMap 2 = 0 := by
  apply (cancel_mono (SphereSingularChainComplex.iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, zero_comp]
  rw [← Category.assoc, cycleLift_i]
  ext
  change firstProjectionChainMap.f 2 ((1 : ℚ) • secondRulingCycle) = 0
  simpa using first_projection_second_ruling_cycle

theorem firstRuling_secondProjection_cyclesMap_zero :
    cycleLift firstRulingCycle firstRulingCycle_boundary_zero ≫
        HomologicalComplex.cyclesMap secondProjectionChainMap 2 = 0 := by
  apply (cancel_mono (SphereSingularChainComplex.iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, zero_comp]
  rw [← Category.assoc, cycleLift_i]
  ext
  change secondProjectionChainMap.f 2 ((1 : ℚ) • firstRulingCycle) = 0
  simpa using second_projection_first_ruling_cycle

theorem firstProjection_firstRulingHomologyMorphism :
    homologyClassMorphism firstRulingCycle firstRulingCycle_boundary_zero ≫
        firstProjectionHomologyMap = sphereFundamentalHomologyMorphism := by
  have hraw :
      (cycleLift firstRulingCycle firstRulingCycle_boundary_zero ≫
          ProductChains.homologyπ 2) ≫
          HomologicalComplex.homologyMap firstProjectionChainMap 2 =
        sphereCycleLift ≫ SphereSingularChainComplex.homologyπ 2 := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, firstRuling_cyclesMap_eq_sphereCycleLift]
  exact hraw

theorem secondProjection_secondRulingHomologyMorphism :
    homologyClassMorphism secondRulingCycle secondRulingCycle_boundary_zero ≫
        secondProjectionHomologyMap = sphereFundamentalHomologyMorphism := by
  have hraw :
      (cycleLift secondRulingCycle secondRulingCycle_boundary_zero ≫
          ProductChains.homologyπ 2) ≫
          HomologicalComplex.homologyMap secondProjectionChainMap 2 =
        sphereCycleLift ≫ SphereSingularChainComplex.homologyπ 2 := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, secondRuling_cyclesMap_eq_sphereCycleLift]
  exact hraw

theorem firstProjection_secondRulingHomologyMorphism_zero :
    homologyClassMorphism secondRulingCycle secondRulingCycle_boundary_zero ≫
        firstProjectionHomologyMap = 0 := by
  have hraw :
      (cycleLift secondRulingCycle secondRulingCycle_boundary_zero ≫
          ProductChains.homologyπ 2) ≫
          HomologicalComplex.homologyMap firstProjectionChainMap 2 = 0 := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, secondRuling_firstProjection_cyclesMap_zero, zero_comp]
  exact hraw

theorem secondProjection_firstRulingHomologyMorphism_zero :
    homologyClassMorphism firstRulingCycle firstRulingCycle_boundary_zero ≫
        secondProjectionHomologyMap = 0 := by
  have hraw :
      (cycleLift firstRulingCycle firstRulingCycle_boundary_zero ≫
          ProductChains.homologyπ 2) ≫
          HomologicalComplex.homologyMap secondProjectionChainMap 2 = 0 := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, firstRuling_secondProjection_cyclesMap_zero, zero_comp]
  exact hraw

theorem firstProjection_firstRulingHomologyClass :
    firstProjectionHomologyMap firstRulingHomologyClass =
      sphereFundamentalHomologyClass := by
  change (homologyClassMorphism firstRulingCycle firstRulingCycle_boundary_zero ≫
    firstProjectionHomologyMap) 1 = sphereFundamentalHomologyMorphism 1
  rw [firstProjection_firstRulingHomologyMorphism]

theorem secondProjection_secondRulingHomologyClass :
    secondProjectionHomologyMap secondRulingHomologyClass =
      sphereFundamentalHomologyClass := by
  change (homologyClassMorphism secondRulingCycle secondRulingCycle_boundary_zero ≫
    secondProjectionHomologyMap) 1 = sphereFundamentalHomologyMorphism 1
  rw [secondProjection_secondRulingHomologyMorphism]

theorem firstProjection_secondRulingHomologyClass_zero :
    firstProjectionHomologyMap secondRulingHomologyClass = 0 := by
  change (homologyClassMorphism secondRulingCycle secondRulingCycle_boundary_zero ≫
    firstProjectionHomologyMap) 1 = 0
  rw [firstProjection_secondRulingHomologyMorphism_zero]
  rfl

theorem secondProjection_firstRulingHomologyClass_zero :
    secondProjectionHomologyMap firstRulingHomologyClass = 0 := by
  change (homologyClassMorphism firstRulingCycle firstRulingCycle_boundary_zero ≫
    secondProjectionHomologyMap) 1 = 0
  rw [secondProjection_firstRulingHomologyMorphism_zero]
  rfl

theorem rulingHomologyMap_injective_of_fundamentalClass_ne_zero
    (hfundamental : sphereFundamentalHomologyClass ≠ 0) :
    Function.Injective rulingHomologyMap := by
  intro x y hxy
  have hdifference : rulingHomologyMap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hfirstImage := congrArg
    (fun homologyClass => firstProjectionHomologyMap homologyClass) hdifference
  have hsecondImage := congrArg
    (fun homologyClass => secondProjectionHomologyMap homologyClass) hdifference
  have hfirstCoefficient : (x - y) 0 = 0 := by
    have : (x - y) 0 • sphereFundamentalHomologyClass = 0 := by
      simpa [rulingHomologyMap, firstProjection_firstRulingHomologyClass,
        firstProjection_secondRulingHomologyClass_zero] using hfirstImage
    exact (smul_eq_zero.mp this).resolve_right hfundamental
  have hsecondCoefficient : (x - y) 1 = 0 := by
    have : (x - y) 1 • sphereFundamentalHomologyClass = 0 := by
      simpa [rulingHomologyMap, secondProjection_secondRulingHomologyClass,
        secondProjection_firstRulingHomologyClass_zero] using hsecondImage
    exact (smul_eq_zero.mp this).resolve_right hfundamental
  funext index
  fin_cases index
  · exact sub_eq_zero.mp (by simpa using hfirstCoefficient)
  · exact sub_eq_zero.mp (by simpa using hsecondCoefficient)

section Audit

#print axioms constantSphereChainMap_fundamentalCandidate_zero
#print axioms firstProjection_firstRulingHomologyClass
#print axioms firstProjection_secondRulingHomologyClass_zero
#print axioms tetrahedralHomologyRealization_injective_iff
#print axioms fundamentalClass_mem_obstruction_iff
#print axioms rulingHomologyMap_injective_of_fundamentalClass_ne_zero

end Audit

end Soma.Holonics.Millennium.HodgeSphereProductRulingProjections
