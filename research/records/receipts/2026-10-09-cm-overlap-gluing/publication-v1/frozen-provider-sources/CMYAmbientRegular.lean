import CMYAmbientEquations
import CMGraphPrincipalCharts
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! Regularity is proved in the actual Y ambient tensor ring through the
monic cubic free extension. No tensor-ring domain assumption is used. -/
noncomputable section
open scoped TensorProduct
open Polynomial
namespace Holonics.Hodge.CMGraphSource

abbrev YCoefficientRing := YChartCubicRing ⊗[ℂ] ℂ[X]
def yCoefficientEquiv : YCoefficientRing ≃ₐ[YChartCubicRing] YChartCubicRing[X] :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : YChartCubicRing ≃ₐ[YChartCubicRing] YChartCubicRing)
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm).trans
      ((MvPolynomial.algebraTensorAlgEquiv ℂ YChartCubicRing).trans
        (MvPolynomial.uniqueAlgEquiv YChartCubicRing (Fin 1)))
def yCoefficientEquation (c : YChartCubicRing) : YCoefficientRing := 1 ⊗ₜ X - c ⊗ₜ 1

theorem yCoefficientEquation_image (c : YChartCubicRing) :
    yCoefficientEquiv (yCoefficientEquation c) = X - C c := by
  simp [yCoefficientEquiv, yCoefficientEquation,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.uniqueAlgEquiv_symm_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]

theorem yCoefficientEquation_nonzero (c : YChartCubicRing) : yCoefficientEquation c ≠ 0 := by
  intro h
  have he := congrArg (fun p => coeff (yCoefficientEquiv p) 1) h
  rw [yCoefficientEquation_image, map_zero] at he
  simp at he

def yBaseChangedPolynomial : YCoefficientRing[X] :=
  yMonicCubic.map Algebra.TensorProduct.includeRight.toRingHom
abbrev YFreeRing := AdjoinRoot yBaseChangedPolynomial
def yFreeEquiv : YProductRing ≃ₐ[YChartCubicRing] YFreeRing :=
  AdjoinRoot.tensorAlgEquiv yMonicCubic yBaseChangedPolynomial rfl

theorem yFreeEquiv_b_difference (c : YChartCubicRing) :
    yFreeEquiv (yRight yAmbientB - yLeft c) =
      AdjoinRoot.of yBaseChangedPolynomial (yCoefficientEquation c) := by
  rw [map_sub]
  have hl : yFreeEquiv (yLeft c) = AdjoinRoot.of yBaseChangedPolynomial (c ⊗ₜ 1) := by
    change yFreeEquiv (algebraMap YChartCubicRing YProductRing c) = _
    rw [AlgEquiv.commutes]
    rfl
  have hr : yFreeEquiv (yRight yAmbientB) =
      AdjoinRoot.of yBaseChangedPolynomial (1 ⊗ₜ X) :=
    AdjoinRoot.tensorAlgEquiv_of _ _ rfl
  rw [hl, hr, yCoefficientEquation, map_sub]

theorem yB_difference_regular (c : YChartCubicRing) : IsRegular (yRight yAmbientB - yLeft c) := by
  let : IsDomain YCoefficientRing :=
    MulEquiv.isDomain YChartCubicRing[X] yCoefficientEquiv.toRingEquiv.toMulEquiv
  have hm : yBaseChangedPolynomial.Monic := yMonicCubic_monic.map _
  let : Module.IsTorsionFree YCoefficientRing YFreeRing := (AdjoinRoot.powerBasis' hm).basis.isTorsionFree
  have hc : IsRegular (yCoefficientEquation c) := IsRegular.of_ne_zero (yCoefficientEquation_nonzero c)
  have hq : IsRegular (AdjoinRoot.of yBaseChangedPolynomial (yCoefficientEquation c)) := by
    rw [← isLeftRegular_iff_isRegular]
    intro x y hxy
    have hsc := @Module.IsTorsionFree.isSMulRegular YCoefficientRing YFreeRing
      (inferInstance : Semiring YCoefficientRing) (inferInstance : AddCommMonoid YFreeRing)
      (inferInstance : Module YCoefficientRing YFreeRing)
      (inferInstance : Module.IsTorsionFree YCoefficientRing YFreeRing) (yCoefficientEquation c) hc
    apply hsc
    simpa only [Algebra.smul_def, AdjoinRoot.algebraMap_eq] using hxy
  rw [← isLeftRegular_iff_isRegular]
  intro x y hxy
  apply yFreeEquiv.injective
  apply hq.1
  simpa only [← yFreeEquiv_b_difference, ← map_mul] using congrArg yFreeEquiv hxy

theorem yGraphBEquation_regular : IsRegular yGraphBEquation := by
  have h : yRight yAmbientB - yLeft ((-Complex.I) • yAmbientB) = yGraphBEquation := by
    simp only [Algebra.smul_def, map_mul, map_neg, AlgHom.commutes, neg_mul, sub_neg_eq_add]
    rfl
  rw [← h]
  exact yB_difference_regular _
theorem yDiagonalBEquation_regular : IsRegular yDiagonalBEquation := yB_difference_regular _

abbrev YGraphPAway := Localization.Away yGraphP
abbrev YGraphQAway := Localization.Away yGraphQ
abbrev YDiagonalPAway := Localization.Away yDiagonalP
abbrev YDiagonalQAway := Localization.Away yDiagonalQ

theorem yGraphIdeal_P_face : yGraphIdeal.map (algebraMap YProductRing YGraphPAway) =
    Ideal.span {algebraMap YProductRing YGraphPAway yGraphBEquation} := by
  rw [yGraphIdeal_eq_two_equations, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [Ideal.span_pair_comm]
  exact two_equations_principal_of_unit _ yGraphBEquation yGraphAEquation yGraphQ yGraphP
    yGraph_difference_relation.symm (IsLocalization.Away.algebraMap_isUnit _)
theorem yGraphIdeal_Q_face : yGraphIdeal.map (algebraMap YProductRing YGraphQAway) =
    Ideal.span {algebraMap YProductRing YGraphQAway yGraphAEquation} := by
  rw [yGraphIdeal_eq_two_equations, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  exact two_equations_principal_of_unit _ yGraphAEquation yGraphBEquation yGraphP yGraphQ
    yGraph_difference_relation (IsLocalization.Away.algebraMap_isUnit _)
theorem yDiagonalIdeal_P_face : yDiagonalIdeal.map (algebraMap YProductRing YDiagonalPAway) =
    Ideal.span {algebraMap YProductRing YDiagonalPAway yDiagonalBEquation} := by
  rw [yDiagonalIdeal_eq_two_equations, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [Ideal.span_pair_comm]
  exact two_equations_principal_of_unit _ yDiagonalBEquation yDiagonalAEquation yDiagonalQ yDiagonalP
    yDiagonal_difference_relation.symm (IsLocalization.Away.algebraMap_isUnit _)
theorem yDiagonalIdeal_Q_face : yDiagonalIdeal.map (algebraMap YProductRing YDiagonalQAway) =
    Ideal.span {algebraMap YProductRing YDiagonalQAway yDiagonalAEquation} := by
  rw [yDiagonalIdeal_eq_two_equations, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  exact two_equations_principal_of_unit _ yDiagonalAEquation yDiagonalBEquation yDiagonalP yDiagonalQ
    yDiagonal_difference_relation (IsLocalization.Away.algebraMap_isUnit _)

theorem yGraphB_P_regular : IsRegular (algebraMap YProductRing YGraphPAway yGraphBEquation) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers yGraphP) YGraphPAway
    (isRegular_iff_mem_nonZeroDivisors.mp yGraphBEquation_regular)
theorem yGraphA_Q_regular : IsRegular (algebraMap YProductRing YGraphQAway yGraphAEquation) := by
  have hb : IsRegular (algebraMap YProductRing YGraphQAway yGraphBEquation) := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers yGraphQ) YGraphQAway
      (isRegular_iff_mem_nonZeroDivisors.mp yGraphBEquation_regular)
  have he := congrArg (algebraMap YProductRing YGraphQAway) yGraph_difference_relation
  simp only [map_mul] at he
  exact (he.symm ▸ hb.mul (IsLocalization.Away.algebraMap_isUnit yGraphQ).isRegular).of_mul_left
theorem yDiagonalB_P_regular : IsRegular (algebraMap YProductRing YDiagonalPAway yDiagonalBEquation) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers yDiagonalP) YDiagonalPAway
    (isRegular_iff_mem_nonZeroDivisors.mp yDiagonalBEquation_regular)
theorem yDiagonalA_Q_regular : IsRegular (algebraMap YProductRing YDiagonalQAway yDiagonalAEquation) := by
  have hb : IsRegular (algebraMap YProductRing YDiagonalQAway yDiagonalBEquation) := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers yDiagonalQ) YDiagonalQAway
      (isRegular_iff_mem_nonZeroDivisors.mp yDiagonalBEquation_regular)
  have he := congrArg (algebraMap YProductRing YDiagonalQAway) yDiagonal_difference_relation
  simp only [map_mul] at he
  exact (he.symm ▸ hb.mul (IsLocalization.Away.algebraMap_isUnit yDiagonalQ).isRegular).of_mul_left

#print axioms yB_difference_regular
#print axioms yGraphBEquation_regular
#print axioms yDiagonalBEquation_regular
#print axioms yGraphIdeal_P_face
#print axioms yGraphIdeal_Q_face
#print axioms yDiagonalIdeal_P_face
#print axioms yDiagonalIdeal_Q_face
#print axioms yGraphB_P_regular
#print axioms yGraphA_Q_regular
#print axioms yDiagonalB_P_regular
#print axioms yDiagonalA_Q_regular
end Holonics.Hodge.CMGraphSource
