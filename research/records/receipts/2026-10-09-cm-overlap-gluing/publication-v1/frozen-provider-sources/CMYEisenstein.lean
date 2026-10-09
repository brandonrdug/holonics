import CMYChartLocalization
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Tactic.ComputeDegree

/-! The Y cubic is irreducible by the actual Eisenstein criterion at b. -/
noncomputable section
open Polynomial
open scoped Polynomial.Bivariate
namespace Holonics.Hodge.CMGraphSource

def yPlaneBivariateEquiv : ZChartPlane ≃ₐ[ℂ] ℂ[X][Y] :=
  (MvPolynomial.finSuccEquiv ℂ 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)))
@[simp] theorem yPlaneBivariateEquiv_a :
    yPlaneBivariateEquiv (MvPolynomial.X 0) = Polynomial.X := by
  simp [yPlaneBivariateEquiv, MvPolynomial.finSuccEquiv_apply]
@[simp] theorem yPlaneBivariateEquiv_b :
    yPlaneBivariateEquiv (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
  simp [yPlaneBivariateEquiv, MvPolynomial.finSuccEquiv_apply]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, Fin.cases_succ]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

def yMonicCubic : ℂ[X][Y] :=
  Polynomial.X ^ 3 - Polynomial.C (Polynomial.X ^ 2) * Polynomial.X -
    Polynomial.C Polynomial.X
theorem yPlaneBivariateEquiv_cubic :
    yPlaneBivariateEquiv yAffineCubic = -yMonicCubic := by
  simp [yAffineCubic, yMonicCubic]
  ring

theorem yMonicCubic_monic : yMonicCubic.Monic := by
  unfold yMonicCubic
  monicity!
theorem yMonicCubic_natDegree : yMonicCubic.natDegree = 3 := by
  unfold yMonicCubic
  compute_degree!

theorem yMonicCubic_irreducible : Irreducible yMonicCubic := by
  let P : Ideal ℂ[X] := Ideal.span {Polynomial.X}
  have hp : P.IsPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have he : yMonicCubic.IsEisensteinAt P :=
    yMonicCubic_monic.isEisensteinAt_of_mem_of_notMem hp.ne_top (by
      intro n hn
      rw [yMonicCubic_natDegree] at hn
      interval_cases n <;>
        simp only [yMonicCubic, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_C,
          coeff_X, if_true, mul_one] <;>
        simp [P, Ideal.mem_span_singleton]) (by
      simp only [yMonicCubic, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_zero, mul_zero,
        coeff_C_zero, sub_zero]
      dsimp only [P]
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      have hd : (Polynomial.X ^ 2 : ℂ[X]) ∣ Polynomial.X := by simpa using h
      have hn := Polynomial.natDegree_le_of_dvd hd Polynomial.X_ne_zero
      norm_num at hn)
  exact he.irreducible hp yMonicCubic_monic.isPrimitive
    (by rw [yMonicCubic_natDegree]; norm_num)

#print axioms yPlaneBivariateEquiv_cubic
#print axioms yMonicCubic_irreducible
end Holonics.Hodge.CMGraphSource
