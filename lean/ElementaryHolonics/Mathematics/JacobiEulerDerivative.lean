import ElementaryHolonics.Mathematics.JacobiTripleProductKernel

/-!
# Euler differentiation of the Jacobi Laurent coordinate

The Jacobi triple-product kernel retains two independent coordinates: the
outer power-series exponent and the Laurent orientation exponent.  This file
constructs the exact Euler derivative on the latter,

`D(T^m) = m T^m`,

lifts it coefficientwise to the complete bivariate power series, proves the
Leibniz law, and transports the checked triple-product equality through that
receiver.  It is a source construction; no analytic derivative or limit is
postulated.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.JacobiEulerDerivative

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel

abbrev LP := LaurentPolynomial ℤ
abbrev BivariateSeries := PowerSeries LP

/-- Euler differentiation on the Laurent orientation coordinate. -/
def laurentEulerDerivative : LP →+ LP where
  toFun f := (AddMonoidAlgebra.coeff f).sum (fun m c =>
    LaurentPolynomial.C (m * c) * LaurentPolynomial.T m
    )
  map_zero' := by simp
  map_add' f g := by
    rw [AddMonoidAlgebra.coeff_add]
    apply Finsupp.sum_add_index'
    · intro m
      simp
    · intro m c d
      push_cast
      rw [mul_add, map_add, add_mul]

@[simp] theorem laurentEulerDerivative_C_mul_T (c m : ℤ) :
    laurentEulerDerivative
        (LaurentPolynomial.C c * LaurentPolynomial.T m) =
      LaurentPolynomial.C (m * c) * LaurentPolynomial.T m := by
  show (AddMonoidAlgebra.coeff
      (LaurentPolynomial.C c * LaurentPolynomial.T m)).sum
      (fun j d => LaurentPolynomial.C (j * d) * LaurentPolynomial.T j) = _
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.sum_single_index]
  simp

@[simp] theorem laurentEulerDerivative_C (c : ℤ) :
    laurentEulerDerivative (LaurentPolynomial.C c) = 0 := by
  have h : LaurentPolynomial.C c =
      LaurentPolynomial.C c * LaurentPolynomial.T 0 := by simp
  rw [h, laurentEulerDerivative_C_mul_T]
  simp

@[simp] theorem laurentEulerDerivative_T (m : ℤ) :
    laurentEulerDerivative (LaurentPolynomial.T m) =
      LaurentPolynomial.C m * LaurentPolynomial.T m := by
  simpa using laurentEulerDerivative_C_mul_T 1 m

/-- Reading the `m`-oriented coefficient after Euler differentiation returns
the original coefficient multiplied by its signed orientation.  This is the
exact coefficient receiver behind `D(T^m) = m T^m`; it does not invoke an
analytic derivative or an evaluation map. -/
@[simp] theorem coeff_laurentEulerDerivative (m : ℤ) (f : LP) :
    AddMonoidAlgebra.coeff (laurentEulerDerivative f) m =
      m * AddMonoidAlgebra.coeff f m := by
  unfold laurentEulerDerivative
  change AddMonoidAlgebra.coeff
      ((AddMonoidAlgebra.coeff f).sum (fun k c =>
        LaurentPolynomial.C (k * c) * LaurentPolynomial.T k)) m = _
  rw [AddMonoidAlgebra.coeff_finsuppSum]
  simp only [Finsupp.sum_apply]
  unfold Finsupp.sum
  classical
  by_cases hm : m ∈ f.coeff.support
  · rw [Finset.sum_eq_single m]
    · change (LaurentPolynomial.C (m * f.coeff m) * LaurentPolynomial.T m).coeff m = _
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      exact Finsupp.single_eq_same
    · intro b hb hbm
      change (LaurentPolynomial.C (b * f.coeff b) * LaurentPolynomial.T b).coeff m = _
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      exact Finsupp.single_eq_of_ne (Ne.symm hbm)
    · exact fun h => (h hm).elim
  · rw [Finset.sum_eq_zero]
    · rw [Finsupp.notMem_support_iff.mp hm]
      ring
    · intro b hb
      have hbm : b ≠ m := by
        intro h
        subst b
        exact hm hb
      change (LaurentPolynomial.C (b * f.coeff b) * LaurentPolynomial.T b).coeff m = _
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      exact Finsupp.single_eq_of_ne (Ne.symm hbm)

/-- The exact Laurent Leibniz law. -/
theorem laurentEulerDerivative_mul (f g : LP) :
    laurentEulerDerivative (f * g) =
      f * laurentEulerDerivative g + laurentEulerDerivative f * g := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [add_mul, map_add, hp, hq]
      ring
  | C_mul_T m a =>
      induction g using LaurentPolynomial.induction_on' with
      | add p q hp hq =>
          simp only [mul_add, map_add, hp, hq]
          ring
      | C_mul_T k b =>
          have hproduct : LaurentPolynomial.C a * LaurentPolynomial.T m *
                (LaurentPolynomial.C b * LaurentPolynomial.T k) =
              LaurentPolynomial.C (a * b) *
                LaurentPolynomial.T (m + k) := by
            rw [map_mul, LaurentPolynomial.T_add]
            ring
          rw [hproduct]
          simp only [laurentEulerDerivative_C_mul_T]
          have hfirst : LaurentPolynomial.C a * LaurentPolynomial.T m *
                (LaurentPolynomial.C (k * b) * LaurentPolynomial.T k) =
              LaurentPolynomial.C (a * (k * b)) *
                LaurentPolynomial.T (m + k) := by
            simp only [map_mul, LaurentPolynomial.T_add]
            ring
          have hsecond :
              LaurentPolynomial.C (m * a) * LaurentPolynomial.T m *
                  (LaurentPolynomial.C b * LaurentPolynomial.T k) =
                LaurentPolynomial.C ((m * a) * b) *
                  LaurentPolynomial.T (m + k) := by
            simp only [map_mul, LaurentPolynomial.T_add]
            ring
          rw [hfirst, hsecond, ← add_mul, ← map_add]
          congr 2
          ring

/-- Coefficientwise Euler differentiation of the Laurent coordinate. -/
def bivariateEulerDerivative (F : BivariateSeries) : BivariateSeries :=
  PowerSeries.mk fun n => laurentEulerDerivative (PowerSeries.coeff n F)

@[simp] theorem coeff_bivariateEulerDerivative (n : ℕ)
    (F : BivariateSeries) :
    PowerSeries.coeff n (bivariateEulerDerivative F) =
      laurentEulerDerivative (PowerSeries.coeff n F) := by
  simp [bivariateEulerDerivative]

theorem bivariateEulerDerivative_zero :
    bivariateEulerDerivative (0 : BivariateSeries) = 0 := by
  apply PowerSeries.ext
  intro n
  simp

theorem bivariateEulerDerivative_add (F G : BivariateSeries) :
    bivariateEulerDerivative (F + G) =
      bivariateEulerDerivative F + bivariateEulerDerivative G := by
  apply PowerSeries.ext
  intro n
  simp

/-- The exact bivariate Leibniz law, obtained by distributing the Laurent
derivative over every finite Cauchy coefficient population. -/
theorem bivariateEulerDerivative_mul (F G : BivariateSeries) :
    bivariateEulerDerivative (F * G) =
      F * bivariateEulerDerivative G + bivariateEulerDerivative F * G := by
  apply PowerSeries.ext
  intro n
  rw [coeff_bivariateEulerDerivative, PowerSeries.coeff_mul, map_sum,
    map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [coeff_bivariateEulerDerivative]
  exact laurentEulerDerivative_mul _ _

/-- **THE CHECKED JACOBI BODY COMMUTES WITH ORIENTATION DIFFERENTIATION.** -/
theorem jacobi_triple_product_euler_derivative :
    bivariateEulerDerivative lhs = bivariateEulerDerivative rhs := by
  exact congrArg bivariateEulerDerivative jacobi_triple_product

#print axioms laurentEulerDerivative_mul
#print axioms coeff_laurentEulerDerivative
#print axioms bivariateEulerDerivative_mul
#print axioms jacobi_triple_product_euler_derivative

end Soma.Holonics.Mathematics.JacobiEulerDerivative
