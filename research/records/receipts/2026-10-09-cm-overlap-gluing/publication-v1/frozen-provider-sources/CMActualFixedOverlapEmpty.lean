import CMActualFixedOpenCover
import CMZChartOtherOpen

/-! Exclude the actual fixed overlap. The global restriction/quotient square
is used first; vanishing of Y/Z in the actual fixed quotient then excludes
the Y basic open. This is not an inference from the two scalar dimensions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zActualFixedQuotient_ambient_square :
    zActualFixedChartQuotientIso.inv ≫ zFixedOpenMap ≫ cmFixedInclusion ≫ cubicEmbedding =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk zFixedDifferenceIdeal)) ≫
        Spec.map (CommRingCat.ofHom zChartToCurve) ≫
          Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) := by
  change zActualFixedChartQuotientIso.inv ≫
    pullback.fst cmFixedInclusion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ≫
      cmFixedInclusion ≫ cubicEmbedding = _
  rw [pullback.condition_assoc,
    Category.assoc zReducedCubicChartIso.inv zCubicOpen.ι cubicEmbedding,
    zCubicChart_embedding_scheme_square, ← Category.assoc,
    zActualFixedChartQuotientIso_inv_inclusion]

theorem zFixedQuotientPoint_outside_yBasicOpen
    (q : PrimeSpectrum (ZChartSquareRing ⧸ zFixedDifferenceIdeal)) :
    Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num)
      (Spec.map (CommRingCat.ofHom zChartToCurve)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk zFixedDifferenceIdeal)) q)) ∉
      Proj.basicOpen CMGrading yCoordinate := by
  intro h
  apply (zAwayι_mem_yBasicOpen _).mp h
  change Ideal.Quotient.mk zFixedDifferenceIdeal (zChartToCurve (zRatio 1)) ∈ q.asIdeal
  rw [zChartToCurve_ratio_v]
  have hz : Ideal.Quotient.mk zFixedDifferenceIdeal zV = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr zV_mem_fixedDifferenceIdeal
  rw [hz]
  exact q.asIdeal.zero_mem

theorem zActualFixedQuotientPoint_outside_y
    (q : PrimeSpectrum (ZChartSquareRing ⧸ zFixedDifferenceIdeal)) :
    cmFixedInclusion (zFixedOpenMap (zActualFixedChartQuotientIso.inv q)) ∉
      yReducedCubicOpen := by
  change cubicEmbedding (cmFixedInclusion (zFixedOpenMap
    (zActualFixedChartQuotientIso.inv q))) ∉ Proj.basicOpen CMGrading yCoordinate
  have he := congrArg (fun f => f q) zActualFixedQuotient_ambient_square
  change cubicEmbedding (cmFixedInclusion (zFixedOpenMap
    (zActualFixedChartQuotientIso.inv q))) = _ at he
  rw [he]
  exact zFixedQuotientPoint_outside_yBasicOpen q

theorem zActualFixedPoint_outside_y
    (p : (pullback cmFixedInclusion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) : Scheme)) :
    cmFixedInclusion (zFixedOpenMap p) ∉ yReducedCubicOpen := by
  have h := zActualFixedQuotientPoint_outside_y (zActualFixedChartQuotientIso.hom p)
  have he : zActualFixedChartQuotientIso.inv (zActualFixedChartQuotientIso.hom p) = p := by
    change (zActualFixedChartQuotientIso.hom ≫ zActualFixedChartQuotientIso.inv) p = p
    rw [Iso.hom_inv_id]
    rfl
  rwa [he] at h

theorem actualFixed_opens_disjoint :
    Disjoint yFixedOpenMap.opensRange zFixedOpenMap.opensRange := by
  apply disjoint_iff.mpr
  ext p
  change (p ∈ yFixedOpenMap.opensRange ∧ p ∈ zFixedOpenMap.opensRange) ↔ False
  constructor
  · rintro ⟨hy, hz⟩
    change p ∈ Set.range zFixedOpenMap at hz
    obtain ⟨q, rfl⟩ := hz
    rw [yFixedOpen_range] at hy
    exact zActualFixedPoint_outside_y q hy
  · exact False.elim

#print axioms zActualFixedQuotient_ambient_square
#print axioms zActualFixedPoint_outside_y
#print axioms actualFixed_opens_disjoint
end Holonics.Hodge.CMGraphSource
