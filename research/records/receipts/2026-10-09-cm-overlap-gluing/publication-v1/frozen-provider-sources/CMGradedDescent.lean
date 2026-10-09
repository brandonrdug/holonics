import CMGraphHomogeneous
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Genuine graded descent to the projective ambient

The existing linear homogeneous substitution is proved degree-preserving,
and the irrelevant-ideal conditions for both directions are proved from
the explicit inverse. Proj.map therefore constructs an actual scheme
automorphism of P^2. Its cubic zero locus is preserved on homogeneous
prime points. Descending the scheme map to the cubic's quotient or ideal
sheaf, and identifying the two affine charts, remain separate obligations.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Graded

namespace Holonics.Hodge.CMGraphSource

abbrev CMGrading := MvPolynomial.homogeneousSubmodule (Fin 3) ℂ
attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousPullback_preserves_degree (q : ℂ) {n : ℕ}
    {p : HomogeneousRing} (hp : p ∈ CMGrading n) :
    homogeneousPullback q p ∈ CMGrading n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
  have hg : ∀ j : Fin 3,
      (![-MvPolynomial.X 0, MvPolynomial.C q * MvPolynomial.X 1,
        MvPolynomial.X 2] j : HomogeneousRing).IsHomogeneous 1 := by
    intro j
    fin_cases j
    · exact (MvPolynomial.isHomogeneous_X ℂ 0).neg
    · exact MvPolynomial.isHomogeneous_C_mul_X q 1
    · exact MvPolynomial.isHomogeneous_X ℂ 2
  simpa only [homogeneousPullback, one_mul] using hp.aeval _ hg

def gradedIota : CMGrading →+*ᵍ CMGrading where
  __ := homogeneousIota.toRingHom
  map_mem := homogeneousPullback_preserves_degree Complex.I

def gradedInverse : CMGrading →+*ᵍ CMGrading where
  __ := homogeneousInverse.toRingHom
  map_mem := homogeneousPullback_preserves_degree (-Complex.I)

theorem graded_inverse_comp : gradedInverse.comp gradedIota = GradedRingHom.id CMGrading := by
  apply GradedRingHom.ext
  intro p
  exact congrArg (fun f : HomogeneousRing →ₐ[ℂ] HomogeneousRing => f p)
    homogeneous_inverse_comp

theorem graded_comp_inverse : gradedIota.comp gradedInverse = GradedRingHom.id CMGrading := by
  apply GradedRingHom.ext
  intro p
  exact congrArg (fun f : HomogeneousRing →ₐ[ℂ] HomogeneousRing => f p)
    homogeneous_comp_inverse

theorem irrelevant_le_map_iota :
    HomogeneousIdeal.irrelevant CMGrading ≤
      (HomogeneousIdeal.irrelevant CMGrading).map gradedIota := by
  apply (HomogeneousIdeal.irrelevant_le CMGrading).mpr
  intro n hn p hp
  have hmem : gradedInverse p ∈ HomogeneousIdeal.irrelevant CMGrading :=
    HomogeneousIdeal.mem_irrelevant_of_mem CMGrading hn (gradedInverse.map_mem hp)
  have hm := Ideal.mem_map_of_mem gradedIota.toRingHom hmem
  change gradedIota (gradedInverse p) ∈
    (HomogeneousIdeal.irrelevant CMGrading).map gradedIota at hm
  have he := congrArg (fun f : CMGrading →+*ᵍ CMGrading => f p) graded_comp_inverse
  change gradedIota (gradedInverse p) = p at he
  rw [he] at hm
  exact hm

theorem irrelevant_le_map_inverse :
    HomogeneousIdeal.irrelevant CMGrading ≤
      (HomogeneousIdeal.irrelevant CMGrading).map gradedInverse := by
  apply (HomogeneousIdeal.irrelevant_le CMGrading).mpr
  intro n hn p hp
  have hmem : gradedIota p ∈ HomogeneousIdeal.irrelevant CMGrading :=
    HomogeneousIdeal.mem_irrelevant_of_mem CMGrading hn (gradedIota.map_mem hp)
  have hm := Ideal.mem_map_of_mem gradedInverse.toRingHom hmem
  change gradedInverse (gradedIota p) ∈
    (HomogeneousIdeal.irrelevant CMGrading).map gradedInverse at hm
  have he := congrArg (fun f : CMGrading →+*ᵍ CMGrading => f p) graded_inverse_comp
  change gradedInverse (gradedIota p) = p at he
  rw [he] at hm
  exact hm

abbrev CMProjectiveAmbient : Scheme := Proj CMGrading

def projectiveAmbientIota : CMProjectiveAmbient ≅ CMProjectiveAmbient where
  hom := Proj.map gradedIota irrelevant_le_map_iota
  inv := Proj.map gradedInverse irrelevant_le_map_inverse
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [graded_comp_inverse, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [graded_inverse_comp, Proj.map_id]

def cubicProjectiveLocus : Set CMProjectiveAmbient :=
  ProjectiveSpectrum.zeroLocus CMGrading {projectiveCubic}

theorem projectiveAmbientIota_preserves_cubic (p : CMProjectiveAmbient) :
    projectiveAmbientIota.hom p ∈ cubicProjectiveLocus ↔ p ∈ cubicProjectiveLocus := by
  change ({projectiveCubic} : Set HomogeneousRing) ⊆
      (p.asHomogeneousIdeal.comap gradedIota : Set HomogeneousRing) ↔
    ({projectiveCubic} : Set HomogeneousRing) ⊆ p.asHomogeneousIdeal
  simp only [Set.singleton_subset_iff]
  change homogeneousIota projectiveCubic ∈ p.asHomogeneousIdeal ↔
    projectiveCubic ∈ p.asHomogeneousIdeal
  rw [homogeneousIota, homogeneousPullback_cubic Complex.I Complex.I_sq]
  change -projectiveCubic ∈ p.asHomogeneousIdeal.toIdeal ↔
    projectiveCubic ∈ p.asHomogeneousIdeal.toIdeal
  exact neg_mem_iff

#print axioms homogeneousPullback_preserves_degree
#print axioms irrelevant_le_map_iota
#print axioms irrelevant_le_map_inverse
#print axioms projectiveAmbientIota
#print axioms projectiveAmbientIota_preserves_cubic

end Holonics.Hodge.CMGraphSource
