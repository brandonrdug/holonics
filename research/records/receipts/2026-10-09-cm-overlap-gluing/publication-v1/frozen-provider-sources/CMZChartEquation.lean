import CMZChartLocalization

/-!
The normalized cubic in the actual degree-zero Z chart and its prime-spectrum
correspondence. This small owner avoids affine point/class-group imports.
It proves the zero-locus correspondence, without presupposing an ideal-sheaf
identification or a degree-zero quotient grading.
-/
noncomputable section
open HomogeneousLocalization AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubic_degree_three : projectiveCubic ∈ CMGrading 3 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have hx := MvPolynomial.isHomogeneous_X ℂ (0 : Fin 3)
  have hy := MvPolynomial.isHomogeneous_X ℂ (1 : Fin 3)
  have hz := MvPolynomial.isHomogeneous_X ℂ (2 : Fin 3)
  have h1 := (hy.pow 2).mul hz
  have h2 := hx.pow 3
  have h3 := hx.mul (hz.pow 2)
  have hh : (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3 +
      MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 : HomogeneousRing).IsHomogeneous 3 :=
    (h1.sub h2).add h3
  simpa [projectiveCubic, WeierstrassCurve.Projective.polynomial, squareCurve,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh

def zNormalizedCubic : ZChartAway :=
  Away.mk CMGrading (coordinate_degree_one 2) 3 projectiveCubic
    (by simpa using cubic_degree_three)
def zCubicChartIdeal : Ideal ZChartAway := Ideal.span {zNormalizedCubic}

def zAffineCubic : ZChartPlane :=
  MvPolynomial.X 1 ^ 2 - (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 0)

theorem zNormalizedCubic_image : zAwayEquivPlane zNormalizedCubic = zAffineCubic := by
  rw [zAwayEquivPlane_apply, zNormalizedCubic, zAwayToPlane_mk 3 _ cubic_degree_three]
  simp [zDehomogenize, projectiveCubic, WeierstrassCurve.Projective.polynomial,
    squareCurve, zAffineCubic, sub_eq_add_neg]

theorem zChart_correspondence_cubic (q : PrimeSpectrum ZChartAway) :
    (ProjIsoSpecTopComponent.FromSpec.toFun
      (coordinate_degree_one 2) (by norm_num) q).1 ∈ cubicProjectiveLocus ↔
      q ∈ PrimeSpectrum.zeroLocus (zCubicChartIdeal : Set ZChartAway) := by
  change ({projectiveCubic} : Set HomogeneousRing) ⊆
    (ProjIsoSpecTopComponent.FromSpec.carrier.asHomogeneousIdeal
      (coordinate_degree_one 2) (by norm_num) q : Set HomogeneousRing) ↔ _
  simp only [Set.singleton_subset_iff]
  change projectiveCubic ∈
    ProjIsoSpecTopComponent.FromSpec.carrier
      (coordinate_degree_one 2) q ↔ _
  rw [ProjIsoSpecTopComponent.FromSpec.num_mem_carrier_iff
    (coordinate_degree_one 2) (by norm_num) q
    ⟨3, ⟨projectiveCubic, cubic_degree_three⟩,
      ⟨zCoordinate ^ 3, SetLike.pow_mem_graded 3 (coordinate_degree_one 2)⟩, ⟨3, rfl⟩⟩]
  change zNormalizedCubic ∈ q.asIdeal ↔ zCubicChartIdeal ≤ q.asIdeal
  rw [zCubicChartIdeal, Ideal.span_le, Set.singleton_subset_iff]
  rfl

#print axioms cubic_degree_three
#print axioms zNormalizedCubic_image
#print axioms zChart_correspondence_cubic
end Holonics.Hodge.CMGraphSource
