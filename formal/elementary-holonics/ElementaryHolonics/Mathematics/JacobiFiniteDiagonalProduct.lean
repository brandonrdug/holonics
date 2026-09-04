import ElementaryHolonics.Mathematics.JacobiEulerDerivative

/-!
# Finite diagonal specialization of the differentiated Jacobi product

The substitution `a = -q` is not a ring map on every completed bivariate
power series: unrestricted Laurent orientations can send infinitely many
source coefficients to one diagonal.  It is, however, an exact ring map on
each finite polynomial body.  This file constructs that map rather than
treating the missing global evaluator as a library boundary.

For the first `n + 1` Jacobi factors, the inverse-orientation product has a
literal vanishing first factor.  Euler differentiation opens that factor and
returns the neighboring `n`-factor Euler product.  The other two product
families both return the `(n + 1)`-factor Euler product.  Hence the exact
finite return is

`E_{n+1}² E_n`.

This is the algebraic core of Jacobi's cube identity.  The later coefficient
stabilization passage identifies its limit with `E³` and with the already
constructed signed triangular current.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.JacobiFiniteDiagonalProduct

open Soma.Holonics.Mathematics.JacobiEulerDerivative
open Soma.Holonics.Mathematics.JacobiTripleProductKernel

abbrev LaurentBody := LaurentPolynomial ℤ
abbrev PolynomialBody := Polynomial LaurentBody

/-! ## Exact finite diagonal receiver -/

/-- The unit `-T` used to substitute the Laurent orientation `a = -q`. -/
def negativeLaurentGenerator : LaurentBodyˣ where
  val := -LaurentPolynomial.T 1
  inv := -LaurentPolynomial.T (-1)
  val_inv := by
    rw [neg_mul_neg, ← LaurentPolynomial.T_add]
    norm_num
  inv_val := by
    rw [neg_mul_neg, ← LaurentPolynomial.T_add]
    norm_num

@[simp] theorem negativeLaurentGenerator_val :
    (negativeLaurentGenerator : LaurentBody) =
      -LaurentPolynomial.T 1 := by
  simp [negativeLaurentGenerator]

/-- The coefficient chart sends the retained Laurent orientation to `-T`. -/
def coefficientDiagonalHom : LaurentBody →+* LaurentBody :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C negativeLaurentGenerator

/-- Simultaneously send the outer polynomial variable to `T` and the inner
Laurent orientation to `-T`.  A monomial `qⁿaᵐ` therefore returns
`(-1)ᵐTⁿ⁺ᵐ`, including its full signed exponent. -/
def finiteDiagonalHom : PolynomialBody →+* LaurentBody :=
  Polynomial.eval₂RingHom coefficientDiagonalHom (LaurentPolynomial.T 1)

def polynomialQ : PolynomialBody := Polynomial.X
def polynomialA : PolynomialBody :=
  Polynomial.C (LaurentPolynomial.T 1)
def polynomialAInv : PolynomialBody :=
  Polynomial.C (LaurentPolynomial.T (-1))

@[simp] theorem finiteDiagonalHom_q :
    finiteDiagonalHom polynomialQ = LaurentPolynomial.T 1 := by
  simp [finiteDiagonalHom, polynomialQ]

@[simp] theorem finiteDiagonalHom_a :
    finiteDiagonalHom polynomialA = -LaurentPolynomial.T 1 := by
  simp [finiteDiagonalHom, polynomialA, coefficientDiagonalHom,
    negativeLaurentGenerator_val]

@[simp] theorem finiteDiagonalHom_aInv :
    finiteDiagonalHom polynomialAInv = -LaurentPolynomial.T (-1) := by
  simp [finiteDiagonalHom, polynomialAInv, coefficientDiagonalHom,
    negativeLaurentGenerator]

/-! ## Coefficientwise Euler differentiation of the finite body -/

/-- Euler differentiation acts on every Laurent coefficient and retains the
outer polynomial address. -/
def polynomialEulerDerivative : PolynomialBody →+ PolynomialBody where
  toFun p := Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff
      (Finsupp.mapRange.addMonoidHom laurentEulerDerivative
        p.toFinsupp.coeff))
  map_zero' := by
    apply Polynomial.ext
    intro n
    simp
  map_add' p q := by
    apply Polynomial.ext
    intro n
    simp

@[simp] theorem coeff_polynomialEulerDerivative
    (p : PolynomialBody) (n : ℕ) :
    (polynomialEulerDerivative p).coeff n =
      laurentEulerDerivative (p.coeff n) := by
  change laurentEulerDerivative (p.toFinsupp.coeff n) =
    laurentEulerDerivative (p.toFinsupp.coeff n)
  rfl

@[simp] theorem laurentEulerDerivative_zero :
    laurentEulerDerivative (0 : LaurentBody) = 0 :=
  map_zero laurentEulerDerivative

@[simp] theorem laurentEulerDerivative_one :
    laurentEulerDerivative (1 : LaurentBody) = 0 := by
  rw [show (1 : LaurentBody) = LaurentPolynomial.C 1 by simp,
    laurentEulerDerivative_C]

@[simp] theorem polynomialEulerDerivative_C (f : LaurentBody) :
    polynomialEulerDerivative (Polynomial.C f) =
      Polynomial.C (laurentEulerDerivative f) := by
  apply Polynomial.ext
  intro n
  rw [coeff_polynomialEulerDerivative]
  by_cases h : n = 0
  · subst n
    simp
  · simp only [Polynomial.coeff_C, if_neg h]
    exact laurentEulerDerivative_zero

@[simp] theorem polynomialEulerDerivative_X :
    polynomialEulerDerivative (Polynomial.X : PolynomialBody) = 0 := by
  apply Polynomial.ext
  intro n
  rw [coeff_polynomialEulerDerivative]
  by_cases h : 1 = n
  · subst n
    simp [Polynomial.coeff_X]
  · simp [Polynomial.coeff_X, h]

@[simp] theorem polynomialEulerDerivative_one :
    polynomialEulerDerivative (1 : PolynomialBody) = 0 := by
  rw [show (1 : PolynomialBody) = Polynomial.C 1 by simp,
    polynomialEulerDerivative_C]
  simpa using congrArg Polynomial.C laurentEulerDerivative_one

/-- The finite coefficientwise Euler operator obeys the exact Leibniz law. -/
theorem polynomialEulerDerivative_mul (p q : PolynomialBody) :
    polynomialEulerDerivative (p * q) =
      p * polynomialEulerDerivative q + polynomialEulerDerivative p * q := by
  apply Polynomial.ext
  intro n
  simp only [coeff_polynomialEulerDerivative, Polynomial.coeff_mul, map_sum,
    laurentEulerDerivative_mul, Finset.sum_add_distrib]
  simp only [Polynomial.coeff_add, Polynomial.coeff_mul,
    coeff_polynomialEulerDerivative]

@[simp] theorem polynomialEulerDerivative_q :
    polynomialEulerDerivative polynomialQ = 0 :=
  polynomialEulerDerivative_X

@[simp] theorem polynomialEulerDerivative_a :
    polynomialEulerDerivative polynomialA = polynomialA := by
  simp [polynomialA, polynomialEulerDerivative_C,
    laurentEulerDerivative_T]

@[simp] theorem polynomialEulerDerivative_aInv :
    polynomialEulerDerivative polynomialAInv = -polynomialAInv := by
  simp [polynomialAInv, polynomialEulerDerivative_C,
    laurentEulerDerivative_T]

/-! ## The finite differentiated return -/

/-- The `n`-factor Euler population after diagonal specialization. -/
def finiteEulerProduct (n : ℕ) : LaurentBody :=
  qPoch (LaurentPolynomial.T 2) (LaurentPolynomial.T 2) n

def finitePolynomialP0 (n : ℕ) : PolynomialBody :=
  qPoch (polynomialQ ^ 2) (polynomialQ ^ 2) n

def finitePolynomialP1 (n : ℕ) : PolynomialBody :=
  qPoch (-polynomialQ * polynomialA) (polynomialQ ^ 2) n

def finitePolynomialP3 (n : ℕ) : PolynomialBody :=
  qPoch (-polynomialQ * polynomialAInv) (polynomialQ ^ 2) n

/-- Every finite `q`-Pochhammer population commutes with a ring receiver. -/
theorem map_qPoch {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A Q : R) (n : ℕ) :
    f (qPoch A Q n) = qPoch (f A) (f Q) n := by
  simp [qPoch]

@[simp] theorem finiteDiagonalHom_P0 (n : ℕ) :
    finiteDiagonalHom (finitePolynomialP0 n) = finiteEulerProduct n := by
  rw [finitePolynomialP0, map_qPoch]
  simp [finiteEulerProduct, polynomialQ, finiteDiagonalHom]

@[simp] theorem finiteDiagonalHom_P1 (n : ℕ) :
    finiteDiagonalHom (finitePolynomialP1 n) = finiteEulerProduct n := by
  rw [finitePolynomialP1, map_qPoch]
  have hT : LaurentPolynomial.T (1 : ℤ) ^ 2 =
      (LaurentPolynomial.T 2 : LaurentBody) := by
    rw [pow_two, ← LaurentPolynomial.T_add]
    norm_num
  simp only [map_neg, map_mul, map_pow, finiteDiagonalHom_q,
    finiteDiagonalHom_a, finiteEulerProduct]
  rw [hT]
  congr 1
  rw [neg_mul_neg]
  simpa [pow_two] using hT

@[simp] theorem finiteDiagonalHom_P3_succ (n : ℕ) :
    finiteDiagonalHom (finitePolynomialP3 (n + 1)) = 0 := by
  rw [finitePolynomialP3, qPoch_succ, map_mul]
  have hfirst :
      finiteDiagonalHom (1 - (-polynomialQ * polynomialAInv)) = 0 := by
    rw [map_sub, map_one, map_mul, map_neg, finiteDiagonalHom_q,
      finiteDiagonalHom_aInv]
    rw [neg_mul_neg, ← LaurentPolynomial.T_add]
    norm_num
  rw [hfirst, zero_mul]

/-- Differentiating the vanishing inverse-orientation product opens precisely
its first factor and returns the neighboring Euler population. -/
theorem finiteDiagonalHom_euler_P3_succ (n : ℕ) :
    finiteDiagonalHom
        (polynomialEulerDerivative (finitePolynomialP3 (n + 1))) =
      finiteEulerProduct n := by
  rw [finitePolynomialP3, qPoch_succ, polynomialEulerDerivative_mul]
  simp only [map_add, map_mul]
  have hfirst :
      finiteDiagonalHom (1 - (-polynomialQ * polynomialAInv)) = 0 := by
    rw [map_sub, map_one, map_mul, map_neg, finiteDiagonalHom_q,
      finiteDiagonalHom_aInv]
    rw [neg_mul_neg, ← LaurentPolynomial.T_add]
    norm_num
  have hDfirst :
      finiteDiagonalHom
          (polynomialEulerDerivative
            (1 - (-polynomialQ * polynomialAInv))) = 1 := by
    have hDexpr :
        polynomialEulerDerivative
            (1 - (-polynomialQ * polynomialAInv)) =
          -polynomialQ * polynomialAInv := by
      rw [map_sub, polynomialEulerDerivative_one,
        polynomialEulerDerivative_mul]
      simp only [map_neg, polynomialEulerDerivative_q,
        polynomialEulerDerivative_aInv, neg_zero, zero_mul, add_zero,
        zero_sub]
      ring
    rw [hDexpr, map_mul, map_neg, finiteDiagonalHom_q,
      finiteDiagonalHom_aInv]
    rw [neg_mul_neg, ← LaurentPolynomial.T_add]
    norm_num
  have htail :
      finiteDiagonalHom
          (qPoch ((-polynomialQ * polynomialAInv) *
              (polynomialQ ^ 2)) (polynomialQ ^ 2) n) =
        finiteEulerProduct n := by
    rw [map_qPoch]
    have hT : LaurentPolynomial.T (1 : ℤ) ^ 2 =
        (LaurentPolynomial.T 2 : LaurentBody) := by
      rw [pow_two, ← LaurentPolynomial.T_add]
      norm_num
    simp only [map_mul, map_neg, map_pow, finiteDiagonalHom_q,
      finiteDiagonalHom_aInv, finiteEulerProduct]
    rw [hT]
    congr 1
    rw [neg_mul_neg, ← LaurentPolynomial.T_add]
    norm_num
  rw [hfirst, zero_mul, zero_add, hDfirst, one_mul, htail]

/-- The finite three-factor Jacobi body. -/
def finitePolynomialTripleProduct (n : ℕ) : PolynomialBody :=
  finitePolynomialP0 n * finitePolynomialP1 n * finitePolynomialP3 n

/-- **FINITE JACOBI DERIVATIVE RETURN.**  At `a = -q`, the first two
families return `E_{n+1}` and differentiation opens the vanishing third
family into `E_n`. -/
theorem finiteDiagonalEulerDerivative_tripleProduct (n : ℕ) :
    finiteDiagonalHom
        (polynomialEulerDerivative
          (finitePolynomialTripleProduct (n + 1))) =
      finiteEulerProduct (n + 1) ^ 2 * finiteEulerProduct n := by
  rw [finitePolynomialTripleProduct, polynomialEulerDerivative_mul]
  simp only [map_add, map_mul, finiteDiagonalHom_P0,
    finiteDiagonalHom_P1, finiteDiagonalHom_P3_succ,
    finiteDiagonalHom_euler_P3_succ]
  ring

#print axioms polynomialEulerDerivative_mul
#print axioms finiteDiagonalHom_euler_P3_succ
#print axioms finiteDiagonalEulerDerivative_tripleProduct

end Soma.Holonics.Mathematics.JacobiFiniteDiagonalProduct
