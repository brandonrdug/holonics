import CMGraphRegular

/-! The diagonal ideal of the actual tensor-product coordinate ring, with
its regular principal equation on a neighborhood of the affine origin.
These are ambient equations; the projective ideal-sheaf comparison is
provided separately through actual pullback squares. -/
noncomputable section
open scoped TensorProduct
open Polynomial
namespace Holonics.Hodge.CMGraphSource

def diagonalReceiver : ProductRing →ₐ[ℂ] CurveRing := Algebra.TensorProduct.lmul' ℂ
def diagonalIdeal : Ideal ProductRing := RingHom.ker diagonalReceiver
def diagonalUEquation : ProductRing := graphRight u - graphLeft u
def diagonalVEquation : ProductRing := graphRight v - graphLeft v
def diagonalTwoEquationIdeal : Ideal ProductRing :=
  Ideal.span {diagonalUEquation, diagonalVEquation}
def diagonalCubicFactor : ProductRing :=
  graphRight u ^ 2 + graphRight u * graphLeft u + graphLeft u ^ 2 - 1
def diagonalVSum : ProductRing := graphRight v + graphLeft v

@[simp] theorem diagonalReceiver_left (a : CurveRing) : diagonalReceiver (graphLeft a) = a := by
  simp [diagonalReceiver, graphLeft]
@[simp] theorem diagonalReceiver_right (a : CurveRing) : diagonalReceiver (graphRight a) = a := by
  simp [diagonalReceiver, graphRight]

theorem diagonalIdeal_eq_two_equations : diagonalIdeal = diagonalTwoEquationIdeal := by
  apply le_antisymm
  · let π : ProductRing →ₐ[ℂ] ProductRing ⧸ diagonalTwoEquationIdeal :=
      Ideal.Quotient.mkₐ ℂ diagonalTwoEquationIdeal
    have hx : π diagonalUEquation = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hv : π diagonalVEquation = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hright : π.comp graphRight = π.comp graphLeft := by
      apply curveRing_hom_ext
      · change π (graphRight u) = π (graphLeft u)
        simpa [diagonalUEquation] using sub_eq_zero.mp hx
      · change π (graphRight v) = π (graphLeft v)
        simpa [diagonalVEquation] using sub_eq_zero.mp hv
    have hwhole : π = (π.comp graphLeft).comp diagonalReceiver := by
      apply Algebra.TensorProduct.ext
      · apply AlgHom.ext
        intro a
        simp [graphLeft, diagonalReceiver]
      · apply AlgHom.ext
        intro a
        simpa [graphRight, diagonalReceiver] using AlgHom.congr_fun hright a
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π p = 0
    rw [hwhole]
    change π (graphLeft (diagonalReceiver p)) = 0
    change diagonalReceiver p = 0 at hp
    simp [hp]
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · change diagonalReceiver diagonalUEquation = 0
      simp [diagonalUEquation]
    · rcases Set.mem_singleton_iff.mp hp with rfl
      change diagonalReceiver diagonalVEquation = 0
      simp [diagonalVEquation]

theorem diagonal_difference_relation :
    diagonalUEquation * diagonalCubicFactor = diagonalVEquation * diagonalVSum := by
  have hL : graphLeft v ^ 2 = graphLeft u ^ 3 - graphLeft u := by
    rw [← map_pow, curve_relation, map_sub, map_pow]
  have hR : graphRight v ^ 2 = graphRight u ^ 3 - graphRight u := by
    rw [← map_pow, curve_relation, map_sub, map_pow]
  calc
    _ = graphRight v ^ 2 - graphLeft v ^ 2 := by
      rw [hL, hR]
      unfold diagonalUEquation diagonalCubicFactor
      ring
    _ = _ := by unfold diagonalVEquation diagonalVSum; ring

abbrev DiagonalFactorAway := Localization.Away diagonalCubicFactor

theorem diagonalIdeal_on_factor_face :
    diagonalIdeal.map (algebraMap ProductRing DiagonalFactorAway) =
      Ideal.span {algebraMap ProductRing DiagonalFactorAway diagonalVEquation} := by
  rw [diagonalIdeal_eq_two_equations, diagonalTwoEquationIdeal, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [Ideal.span_pair_comm]
  exact two_equations_principal_of_unit (algebraMap ProductRing DiagonalFactorAway)
    diagonalVEquation diagonalUEquation diagonalVSum diagonalCubicFactor
    diagonal_difference_relation.symm (IsLocalization.Away.algebraMap_isUnit _)

def diagonalCoefficientEquation : GraphCoefficientRing := 1 ⊗ₜ Polynomial.X - u ⊗ₜ 1

theorem diagonalCoefficientEquation_image :
    graphCoefficientEquiv diagonalCoefficientEquation = Polynomial.X - Polynomial.C u := by
  simp [graphCoefficientEquiv, diagonalCoefficientEquation,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.uniqueAlgEquiv_symm_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]

theorem diagonalCoefficientEquation_nonzero : diagonalCoefficientEquation ≠ 0 := by
  intro h
  have he := congrArg (fun p => Polynomial.coeff (graphCoefficientEquiv p) 1) h
  rw [diagonalCoefficientEquation_image, map_zero] at he
  simp at he

theorem graphFreeEquiv_diagonal_equation :
    graphFreeEquiv diagonalUEquation =
      AdjoinRoot.of graphBaseChangedPolynomial diagonalCoefficientEquation := by
  rw [diagonalUEquation, map_sub]
  have hl : graphFreeEquiv (graphLeft u) =
      AdjoinRoot.of graphBaseChangedPolynomial (u ⊗ₜ 1) := by
    change graphFreeEquiv (algebraMap CurveRing ProductRing u) = _
    rw [AlgEquiv.commutes]
    rfl
  have hr : graphFreeEquiv (graphRight u) =
      AdjoinRoot.of graphBaseChangedPolynomial (1 ⊗ₜ Polynomial.X) :=
    AdjoinRoot.tensorAlgEquiv_of _ _ rfl
  rw [hl, hr, diagonalCoefficientEquation, map_sub]

theorem diagonalUEquation_regular : IsRegular diagonalUEquation := by
  let : IsDomain GraphCoefficientRing :=
    MulEquiv.isDomain CurveRing[X] graphCoefficientEquiv.toRingEquiv.toMulEquiv
  have hm : graphBaseChangedPolynomial.Monic := squareCurve.toAffine.monic_polynomial.map _
  let : Module.IsTorsionFree GraphCoefficientRing GraphFreeRing :=
    (AdjoinRoot.powerBasis' hm).basis.isTorsionFree
  have hc : IsRegular diagonalCoefficientEquation :=
    IsRegular.of_ne_zero diagonalCoefficientEquation_nonzero
  have hq : IsRegular (AdjoinRoot.of graphBaseChangedPolynomial diagonalCoefficientEquation) := by
    rw [← isLeftRegular_iff_isRegular]
    intro x y hxy
    have hsc := @Module.IsTorsionFree.isSMulRegular GraphCoefficientRing GraphFreeRing
      (inferInstance : Semiring GraphCoefficientRing)
      (inferInstance : AddCommMonoid GraphFreeRing)
      (inferInstance : Module GraphCoefficientRing GraphFreeRing)
      (inferInstance : Module.IsTorsionFree GraphCoefficientRing GraphFreeRing)
      diagonalCoefficientEquation hc
    apply hsc
    simpa only [Algebra.smul_def, AdjoinRoot.algebraMap_eq] using hxy
  rw [← isLeftRegular_iff_isRegular]
  intro x y hxy
  apply graphFreeEquiv.injective
  apply hq.1
  simpa only [← graphFreeEquiv_diagonal_equation, ← map_mul] using congrArg graphFreeEquiv hxy

theorem diagonalVEquation_regular_on_factor_face :
    IsRegular (algebraMap ProductRing DiagonalFactorAway diagonalVEquation) := by
  have hg : IsRegular (algebraMap ProductRing DiagonalFactorAway diagonalUEquation) := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers diagonalCubicFactor)
      DiagonalFactorAway (isRegular_iff_mem_nonZeroDivisors.mp diagonalUEquation_regular)
  have hc := (IsLocalization.Away.algebraMap_isUnit diagonalCubicFactor
    (S := DiagonalFactorAway)).isRegular
  have he := congrArg (algebraMap ProductRing DiagonalFactorAway) diagonal_difference_relation
  simp only [map_mul] at he
  exact (he ▸ hg.mul hc).of_mul_left

@[simp] theorem graphReceiver_diagonal_v :
    graphReceiver diagonalVEquation = (Complex.I - 1) • v := by
  simp [diagonalVEquation, iota, sub_smul]
@[simp] theorem graphReceiver_diagonal_factor :
    graphReceiver diagonalCubicFactor = u ^ 2 - 1 := by
  simp [diagonalCubicFactor, iota]
  ring

#print axioms diagonalIdeal_eq_two_equations
#print axioms diagonal_difference_relation
#print axioms diagonalIdeal_on_factor_face
#print axioms diagonalUEquation_regular
#print axioms diagonalVEquation_regular_on_factor_face
#print axioms graphReceiver_diagonal_v
#print axioms graphReceiver_diagonal_factor
end Holonics.Hodge.CMGraphSource
