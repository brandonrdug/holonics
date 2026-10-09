import CMZCubicChart
import CMYChartSheaf
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! The actual reduced projective cubic is covered by its Y and Z opens. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_irrelevant_le_of_all_coordinates
    (P : HomogeneousIdeal CMGrading)
    (hX : ∀ j : Fin 3, MvPolynomial.X j ∈ P) :
    HomogeneousIdeal.irrelevant CMGrading ≤ P := by
  have hvars : MvPolynomial.idealOfVars (Fin 3) ℂ ≤ P.toIdeal :=
    Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hX j)
  apply (HomogeneousIdeal.irrelevant_le CMGrading).mpr
  intro n hn p hp
  apply hvars
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 3) ℂ),
    MvPolynomial.mem_pow_idealOfVars_iff]
  intro m hm
  have he := ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp).degree_eq_sum_deg_support hm
  simpa only [Finsupp.degree_apply] using he ▸ hn

theorem cubic_point_chart_cover (p : CMProjectiveAmbient) (hp : p ∈ cubicProjectiveLocus) :
    p ∈ Proj.basicOpen CMGrading yCoordinate ∨ p ∈ Proj.basicOpen CMGrading zCoordinate := by
  by_contra hn
  have hy : yCoordinate ∈ p.asHomogeneousIdeal := by
    have h := (not_or.mp hn).1
    change ¬ (yCoordinate ∉ p.asHomogeneousIdeal) at h
    exact not_not.mp h
  have hz : zCoordinate ∈ p.asHomogeneousIdeal := by
    have h := (not_or.mp hn).2
    change ¬ (zCoordinate ∉ p.asHomogeneousIdeal) at h
    exact not_not.mp h
  have hf : projectiveCubic ∈ p.asHomogeneousIdeal := Set.singleton_subset_iff.mp hp
  have hx3 : (MvPolynomial.X 0 : HomogeneousRing) ^ 3 ∈ p.asHomogeneousIdeal := by
    have h1 := p.asHomogeneousIdeal.toIdeal.mul_mem_right (yCoordinate ^ 2) hz
    have h2 := p.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.X 0)
      (p.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hz 2 (by norm_num))
    have h := p.asHomogeneousIdeal.toIdeal.sub_mem
      (p.asHomogeneousIdeal.toIdeal.add_mem h1 h2) hf
    convert h using 1
    simp [projectiveCubic, WeierstrassCurve.Projective.polynomial, squareCurve,
      yCoordinate, zCoordinate]
    ring
  have hx : (MvPolynomial.X 0 : HomogeneousRing) ∈ p.asHomogeneousIdeal :=
    p.isPrime.mem_of_pow_mem 3 hx3
  apply p.not_irrelevant_le
  apply homogeneous_irrelevant_le_of_all_coordinates
  intro j
  fin_cases j
  · exact hx
  · exact hy
  · exact hz

def yCubicOpen : CMProjectiveCubic.Opens := cubicEmbedding ⁻¹ᵁ yAmbientAffineOpen.1
theorem yCubicOpen_isAffine : IsAffineOpen yCubicOpen :=
  yAmbientAffineOpen.2.preimage cubicEmbedding

theorem cubic_chart_opens_cover (p : CMProjectiveCubic) :
    p ∈ yCubicOpen ∨ p ∈ zCubicOpen := by
  have hr : cubicEmbedding p ∈ cubicProjectiveLocus := by
    have hm : cubicEmbedding p ∈ Set.range cubicEmbedding := ⟨p, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι,
      cubicIdealSheaf, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hm
    exact hm
  exact cubic_point_chart_cover (cubicEmbedding p) hr

#print axioms homogeneous_irrelevant_le_of_all_coordinates
#print axioms cubic_point_chart_cover
#print axioms cubic_chart_opens_cover
end Holonics.Hodge.CMGraphSource
