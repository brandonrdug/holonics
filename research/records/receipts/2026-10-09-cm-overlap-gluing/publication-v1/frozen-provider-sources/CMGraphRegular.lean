import CMGraphPrincipalCharts
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
Regularity of the two concrete affine graph generators. The x equation
is a nonzero polynomial coefficient in a free monic Weierstrass extension.
The second generator is regular on its face by the proved difference
identity and the unit cubic factor. No surface-domain or Cartier predicate
is assumed. The projective chart coverage and CM chart join are separate.
-/
noncomputable section
open scoped TensorProduct Polynomial.Bivariate
open Polynomial
namespace Holonics.Hodge.CMGraphSource

abbrev GraphCoefficientRing := CurveRing ⊗[ℂ] ℂ[X]
def graphCoefficientEquiv : GraphCoefficientRing ≃ₐ[CurveRing] CurveRing[X] :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : CurveRing ≃ₐ[CurveRing] CurveRing)
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm).trans
      ((MvPolynomial.algebraTensorAlgEquiv ℂ CurveRing).trans
        (MvPolynomial.uniqueAlgEquiv CurveRing (Fin 1)))

def graphCoefficientEquation : GraphCoefficientRing := 1 ⊗ₜ Polynomial.X + u ⊗ₜ 1
theorem graphCoefficientEquation_image :
    graphCoefficientEquiv graphCoefficientEquation = Polynomial.X + Polynomial.C u := by
  simp [graphCoefficientEquiv, graphCoefficientEquation,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.uniqueAlgEquiv_symm_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]

theorem graphCoefficientEquation_nonzero : graphCoefficientEquation ≠ 0 := by
  intro h
  have he := congrArg (fun p => Polynomial.coeff (graphCoefficientEquiv p) 1) h
  rw [graphCoefficientEquation_image, map_zero] at he
  simp at he

def graphBaseChangedPolynomial : GraphCoefficientRing[X] :=
  squareCurve.toAffine.polynomial.map Algebra.TensorProduct.includeRight.toRingHom
abbrev GraphFreeRing := AdjoinRoot graphBaseChangedPolynomial
def graphFreeEquiv : ProductRing ≃ₐ[CurveRing] GraphFreeRing :=
  AdjoinRoot.tensorAlgEquiv squareCurve.toAffine.polynomial graphBaseChangedPolynomial rfl

theorem graphFreeEquiv_x_equation :
    graphFreeEquiv graphXEquation = AdjoinRoot.of graphBaseChangedPolynomial graphCoefficientEquation := by
  rw [graphXEquation, map_add]
  have hl : graphFreeEquiv (graphLeft u) =
      AdjoinRoot.of graphBaseChangedPolynomial (u ⊗ₜ 1) := by
    change graphFreeEquiv (algebraMap CurveRing ProductRing u) = _
    rw [AlgEquiv.commutes]
    rfl
  have hr : graphFreeEquiv (graphRight u) =
      AdjoinRoot.of graphBaseChangedPolynomial (1 ⊗ₜ Polynomial.X) :=
    AdjoinRoot.tensorAlgEquiv_of _ _ rfl
  rw [hl, hr, graphCoefficientEquation, map_add]

theorem graphXEquation_regular : IsRegular graphXEquation := by
  let : IsDomain GraphCoefficientRing :=
    MulEquiv.isDomain CurveRing[X] graphCoefficientEquiv.toRingEquiv.toMulEquiv
  have hm : graphBaseChangedPolynomial.Monic :=
    squareCurve.toAffine.monic_polynomial.map _
  let : Module.IsTorsionFree GraphCoefficientRing GraphFreeRing :=
    (AdjoinRoot.powerBasis' hm).basis.isTorsionFree
  have hc : IsRegular graphCoefficientEquation := IsRegular.of_ne_zero graphCoefficientEquation_nonzero
  have hq : IsRegular (AdjoinRoot.of graphBaseChangedPolynomial graphCoefficientEquation) := by
    rw [← isLeftRegular_iff_isRegular]
    intro x y hxy
    have hsc := @Module.IsTorsionFree.isSMulRegular GraphCoefficientRing GraphFreeRing
      (inferInstance : Semiring GraphCoefficientRing)
      (inferInstance : AddCommMonoid GraphFreeRing)
      (inferInstance : Module GraphCoefficientRing GraphFreeRing)
      (inferInstance : Module.IsTorsionFree GraphCoefficientRing GraphFreeRing)
      graphCoefficientEquation hc
    apply hsc
    simpa only [Algebra.smul_def, AdjoinRoot.algebraMap_eq] using hxy
  rw [← isLeftRegular_iff_isRegular]
  intro x y hxy
  apply graphFreeEquiv.injective
  apply hq.1
  simpa only [← graphFreeEquiv_x_equation, ← map_mul] using congrArg graphFreeEquiv hxy

theorem graphXEquation_regular_on_vsum_face :
    IsRegular (algebraMap ProductRing GraphVAway graphXEquation) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers graphVSum) GraphVAway
    (isRegular_iff_mem_nonZeroDivisors.mp graphXEquation_regular)

theorem graphVEquation_regular_on_factor_face :
    IsRegular (algebraMap ProductRing GraphFactorAway graphVEquation) := by
  have hg : IsRegular (algebraMap ProductRing GraphFactorAway graphXEquation) := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers graphCubicFactor) GraphFactorAway
      (isRegular_iff_mem_nonZeroDivisors.mp graphXEquation_regular)
  have hc := (IsLocalization.Away.algebraMap_isUnit graphCubicFactor
    (S := GraphFactorAway)).isRegular
  have he := congrArg (algebraMap ProductRing GraphFactorAway) graph_difference_relation
  simp only [map_mul] at he
  exact (he ▸ hg.mul hc).of_mul_left

#print axioms graphCoefficientEquiv
#print axioms graphXEquation_regular
#print axioms graphXEquation_regular_on_vsum_face
#print axioms graphVEquation_regular_on_factor_face
end Holonics.Hodge.CMGraphSource
