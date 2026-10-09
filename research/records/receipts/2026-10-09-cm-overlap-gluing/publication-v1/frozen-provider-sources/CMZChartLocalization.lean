import CMComplexBase
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
The standard Z chart's actual degree-zero homogeneous localization has
the two-variable polynomial presentation. Reconstruction is proved by
the homogeneous localization's module-generation theorem, with the
denominators retained. No quotient/ideal-sheaf comparison is assumed.
-/
noncomputable section
open HomogeneousLocalization
open scoped BigOperators
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ZChartPlane := MvPolynomial (Fin 2) ℂ
abbrev zCoordinate : HomogeneousRing := MvPolynomial.X 2
theorem coordinate_degree_one (j : Fin 3) : MvPolynomial.X j ∈ CMGrading 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℂ j)
abbrev ZChartAway := Away CMGrading zCoordinate

def zDehomogenize : HomogeneousRing →+* ZChartPlane :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0, MvPolynomial.X 1, 1]
def zAwayToPlane : ZChartAway →+* ZChartPlane :=
  (Localization.awayLift zDehomogenize zCoordinate (by simp [zDehomogenize])).comp
    (algebraMap ZChartAway (Localization.Away zCoordinate))

theorem zAwayToPlane_mk (n : ℕ) (p : HomogeneousRing) (hp : p ∈ CMGrading n) :
    zAwayToPlane (Away.mk CMGrading (coordinate_degree_one 2) n p
      (by simpa using hp)) = zDehomogenize p := by
  simp [zAwayToPlane, Away.val_mk, Localization.awayLift_mk, zDehomogenize]

def zRatio (j : Fin 3) : ZChartAway :=
  Away.mk CMGrading (coordinate_degree_one 2) 1 (MvPolynomial.X j)
    (by simpa using coordinate_degree_one j)
def zChartCoefficient : ℂ →+* ZChartAway :=
  (fromZeroRingHom CMGrading (.powers zCoordinate)).comp cmDegreeZeroEquiv.symm.toRingHom
def zPlaneToAway : ZChartPlane →+* ZChartAway :=
  MvPolynomial.eval₂Hom zChartCoefficient ![zRatio 0, zRatio 1]

@[simp] theorem zAwayToPlane_ratio (j : Fin 3) :
    zAwayToPlane (zRatio j) = ![MvPolynomial.X 0, MvPolynomial.X 1, 1] j := by
  rw [zRatio, zAwayToPlane_mk 1 _ (coordinate_degree_one j)]
  simp [zDehomogenize]
@[simp] theorem zAwayToPlane_coefficient (c : ℂ) :
    zAwayToPlane (zChartCoefficient c) = MvPolynomial.C c := by
  change zAwayToPlane (Away.mk CMGrading (coordinate_degree_one 2) 0
    (MvPolynomial.C c) _) = _
  rw [zAwayToPlane_mk 0 _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_C _ c))]
  simp [zDehomogenize]

theorem zAway_plane_inverse : zAwayToPlane.comp zPlaneToAway = RingHom.id ZChartPlane := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [zPlaneToAway]
  · intro j
    fin_cases j <;> simp [zPlaneToAway]

theorem zRatio_denominator : zRatio 2 = 1 := by
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [zRatio, Away.val_mk]

def zRangeAlgebra : Subalgebra (CMGrading 0) ZChartAway where
  __ := zPlaneToAway.rangeS
  algebraMap_mem' c := by
    refine ⟨MvPolynomial.C (cmDegreeZeroEquiv c), ?_⟩
    simp only [zPlaneToAway, MvPolynomial.eval₂Hom_C]
    change fromZeroRingHom CMGrading (.powers zCoordinate)
      (cmDegreeZeroEquiv.symm (cmDegreeZeroEquiv c)) = _
    rw [RingEquiv.symm_apply_apply]
    rfl

theorem homogeneous_coordinates_generate :
    Algebra.adjoin (CMGrading 0) (Set.range (MvPolynomial.X : Fin 3 → HomogeneousRing)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact Subalgebra.algebraMap_mem _ (cmDegreeZeroEquiv.symm c)
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self j))

theorem zRatio_in_range (j : Fin 3) : zRatio j ∈ zRangeAlgebra := by
  fin_cases j
  · exact ⟨MvPolynomial.X 0, by simp [zPlaneToAway]⟩
  · exact ⟨MvPolynomial.X 1, by simp [zPlaneToAway]⟩
  · change zRatio 2 ∈ zRangeAlgebra
    rw [zRatio_denominator]
    exact Subalgebra.one_mem _

theorem zMonomial_fraction (a : ℕ) (ai : Fin 3 → ℕ)
    (hai : ∑ j, ai j = a) :
    Away.mk CMGrading (coordinate_degree_one 2) a
      (∏ j, MvPolynomial.X j ^ ai j)
      (by simpa [hai] using (SetLike.prod_pow_mem_graded CMGrading
        (F := Finset.univ) (fun _ => (1 : ℕ)) (fun j => MvPolynomial.X j) ai
        (fun j _ => coordinate_degree_one j))) =
      ∏ j, zRatio j ^ ai j := by
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  change Localization.mk _ _ =
    (algebraMap ZChartAway (Localization.Away zCoordinate)) (∏ j, zRatio j ^ ai j)
  rw [map_prod]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply, zRatio,
    Away.val_mk, Localization.mk_pow, Localization.mk_prod]
  congr 1
  apply Subtype.ext
  rw [Finset.prod_pow_eq_pow_sum]
  simp [hai]

theorem zPlaneToAway_surjective : Function.Surjective zPlaneToAway := by
  have hspan := Away.span_mk_prod_pow_eq_top (coordinate_degree_one 2)
    (v := (MvPolynomial.X : Fin 3 → HomogeneousRing)) homogeneous_coordinates_generate
    (fun _ => 1) coordinate_degree_one
  have hle : Submodule.span (CMGrading 0)
      { Away.mk CMGrading (coordinate_degree_one 2) a (∏ j, MvPolynomial.X j ^ ai j)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ (fun j _ => coordinate_degree_one j)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ j, ai j • (1 : ℕ) = a • (1 : ℕ)) } ≤
      zRangeAlgebra.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro p ⟨a, ai, hai, rfl⟩
    have he : ∑ j, ai j = a := by simpa using hai
    rw [zMonomial_fraction a ai he]
    exact Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (zRatio_in_range j) _)
  rw [hspan] at hle
  intro p
  exact hle (Submodule.mem_top : p ∈ (⊤ : Submodule (CMGrading 0) ZChartAway))

def zAwayEquivPlane : ZChartAway ≃+* ZChartPlane :=
  (RingEquiv.ofBijective zPlaneToAway
    ⟨(Function.LeftInverse.injective (f := zPlaneToAway) (g := zAwayToPlane) (fun p => congrArg
      (fun f : ZChartPlane →+* ZChartPlane => f p) zAway_plane_inverse)),
      zPlaneToAway_surjective⟩).symm

theorem zAwayEquivPlane_apply (p : ZChartAway) : zAwayEquivPlane p = zAwayToPlane p := by
  obtain ⟨q, rfl⟩ := zPlaneToAway_surjective p
  have he := congrArg (fun f : ZChartPlane →+* ZChartPlane => f q) zAway_plane_inverse
  have hi : zAwayEquivPlane (zPlaneToAway q) = q :=
    (RingEquiv.ofBijective zPlaneToAway _).symm_apply_apply q
  exact hi.trans he.symm

#print axioms zAway_plane_inverse
#print axioms zMonomial_fraction
#print axioms zPlaneToAway_surjective
#print axioms zAwayEquivPlane
#print axioms zAwayEquivPlane_apply
end Holonics.Hodge.CMGraphSource
