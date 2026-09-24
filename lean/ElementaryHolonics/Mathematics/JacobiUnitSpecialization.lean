import ElementaryHolonics.Mathematics.JacobiTripleProductKernel

/-!
# Exact unit specializations of the bivariate Jacobi body

The Jacobi kernel retains the square exponent and Laurent orientation as
different coordinates.  This file constructs the missing coefficientwise
receiver which sends the Laurent generator to an actual unit `ε = ±1` while
retaining the complete outer power series.  It is a ring homomorphism, so the
Jacobi product identity may be transported before any coefficient is read.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.JacobiUnitSpecialization

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel

abbrev LP := LaurentPolynomial ℤ
abbrev IntegerSeries := PowerSeries ℤ
abbrev BivariateSeries := PowerSeries LP

/-- Evaluation of the Laurent orientation at an invertible integer sign. -/
def laurentUnitReceiver (ε : ℤˣ) : LP →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) ε

/-- Coefficientwise lift of the Laurent sign receiver to the complete Jacobi
power-series body. -/
def jacobiUnitReceiver (ε : ℤˣ) : BivariateSeries →+* IntegerSeries :=
  PowerSeries.map (laurentUnitReceiver ε)

/-- The coefficient topology on the returned integer power series.  Naming it
keeps the continuity witness stable when the Jacobi kernel's Laurent
coefficient topology is active at the same time. -/
noncomputable abbrev integerSeriesPiTop : TopologicalSpace IntegerSeries :=
  PowerSeries.WithPiTopology.instTopologicalSpace ℤ

/-- The unit receiver is continuous for the coefficient topologies.  This is
the missing transport receipt required to commute it with the complete
Jacobi infinite products. -/
theorem jacobiUnitReceiver_continuous (ε : ℤˣ) :
    letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
    letI : TopologicalSpace BivariateSeries := piTop
    Continuous (jacobiUnitReceiver ε) := by
  letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
  letI : TopologicalSpace BivariateSeries := piTop
  change Continuous (fun F : BivariateSeries =>
    fun d : Unit →₀ ℕ => laurentUnitReceiver ε (F d))
  apply continuous_pi
  intro i
  have heval : Continuous (laurentUnitReceiver ε) :=
    continuous_of_discreteTopology
  have hc : Continuous (fun F : BivariateSeries =>
      laurentUnitReceiver ε (MvPowerSeries.coeff i F)) :=
    heval.comp
      (MvPowerSeries.WithPiTopology.continuous_coeff
        (LaurentPolynomial ℤ) i)
  convert hc using 1
  funext F
  congr 1

/-- On the returned integer-series chart, a multipliable Jacobi product is
the ordinary unconditional product of its complete factor population. -/
theorem integer_qPochhammerInf_eq_tprod (A Q : IntegerSeries)
    (hm : letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
      Multipliable (fun n => 1 - A * Q ^ n)) :
    letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
    qPochhammerInf A Q = ∏' n, (1 - A * Q ^ n) := by
  letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
  letI : T2Space IntegerSeries :=
    PowerSeries.WithPiTopology.instT2Space ℤ
  exact tprod_eq_of_multipliable_unconditional hm

/-- **THE UNIT RECEIVER COMMUTES WITH THE COMPLETE JACOBI PRODUCT.**  This is
proved from the product population's multipliability and an explicit
continuity receipt; it is not a finite-prefix convention. -/
theorem jacobiUnitReceiver_qPochhammerInf (ε : ℤˣ) (A Q : BivariateSeries)
    (hm : letI : TopologicalSpace BivariateSeries := piTop
      Multipliable (fun n => 1 - A * Q ^ n)) :
    letI : TopologicalSpace BivariateSeries := piTop
    letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
    jacobiUnitReceiver ε (qPochhammerInf A Q) =
      qPochhammerInf (jacobiUnitReceiver ε A)
        (jacobiUnitReceiver ε Q) := by
  letI : TopologicalSpace BivariateSeries := piTop
  letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
  letI : T2Space IntegerSeries :=
    PowerSeries.WithPiTopology.instT2Space ℤ
  have hcont : Continuous (jacobiUnitReceiver ε) :=
    jacobiUnitReceiver_continuous ε
  have hterm (n : ℕ) :
      jacobiUnitReceiver ε (1 - A * Q ^ n) =
        1 - jacobiUnitReceiver ε A * (jacobiUnitReceiver ε Q) ^ n := by
    simp
  have hmTarget : Multipliable (fun n =>
      1 - jacobiUnitReceiver ε A * (jacobiUnitReceiver ε Q) ^ n) := by
    exact (hm.map (jacobiUnitReceiver ε) hcont).congr (fun n => hterm n)
  rw [qPochhammerInf_eq_tprod A Q hm,
    integer_qPochhammerInf_eq_tprod _ _ hmTarget]
  calc
    jacobiUnitReceiver ε (∏' n, (1 - A * Q ^ n)) =
        ∏' n, jacobiUnitReceiver ε (1 - A * Q ^ n) :=
      hm.map_tprod (jacobiUnitReceiver ε) hcont
    _ = ∏' n,
        (1 - jacobiUnitReceiver ε A * (jacobiUnitReceiver ε Q) ^ n) := by
      congr 1
      funext n
      exact hterm n

@[simp] theorem coeff_jacobiUnitReceiver (ε : ℤˣ)
    (F : BivariateSeries) (n : ℕ) :
    PowerSeries.coeff n (jacobiUnitReceiver ε F) =
      laurentUnitReceiver ε (PowerSeries.coeff n F) := by
  simp [jacobiUnitReceiver]

@[simp] theorem laurentUnitReceiver_C_mul_T
    (ε : ℤˣ) (c m : ℤ) :
    laurentUnitReceiver ε
        (LaurentPolynomial.C c * LaurentPolynomial.T m) =
      c * (ε ^ m).val := by
  simp [laurentUnitReceiver]

/-- The receiver reads every retained Laurent orientation exactly once. -/
theorem laurentUnitReceiver_eq_finsuppSum (ε : ℤˣ) (f : LP) :
    laurentUnitReceiver ε f =
      (AddMonoidAlgebra.coeff f).sum (fun m c => c * (ε ^ m).val) := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      rw [AddMonoidAlgebra.coeff_add]
      apply (Finsupp.sum_add_index' (f := AddMonoidAlgebra.coeff p)
        (g := AddMonoidAlgebra.coeff q)
        (h := fun m c => c * (ε ^ m).val) ?_ ?_).symm
      · intro m
        simp only [zero_mul]
      · intro m c d
        ring
  | C_mul_T m c =>
      rw [laurentUnitReceiver_C_mul_T]
      change c * (ε ^ m).val =
        (AddMonoidAlgebra.coeff (LaurentPolynomial.C c * LaurentPolynomial.T m)).sum
          (fun m c => c * (ε ^ m).val)
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      rw [AddMonoidAlgebra.sum_single_index]
      simp

@[simp] theorem jacobiUnitReceiver_q (ε : ℤˣ) :
    jacobiUnitReceiver ε q = PowerSeries.X := by
  simp [jacobiUnitReceiver, q]

@[simp] theorem jacobiUnitReceiver_a (ε : ℤˣ) :
    jacobiUnitReceiver ε a = PowerSeries.C ε.val := by
  simp [jacobiUnitReceiver, a, laurentUnitReceiver]

@[simp] theorem jacobiUnitReceiver_aI (ε : ℤˣ) :
    jacobiUnitReceiver ε aI = PowerSeries.C (ε⁻¹).val := by
  simp [jacobiUnitReceiver, aI, laurentUnitReceiver]

/-- The complete Jacobi product after a unit specialization.  Every infinite
factor family is transported through the continuous receiver before the
three returned products are multiplied. -/
theorem jacobiUnitReceiver_lhs (ε : ℤˣ) :
    letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
    jacobiUnitReceiver ε lhs =
      qPochhammerInf (PowerSeries.X ^ 2) (PowerSeries.X ^ 2) *
        qPochhammerInf (-PowerSeries.X * PowerSeries.C ε.val)
          (PowerSeries.X ^ 2) *
        qPochhammerInf (-PowerSeries.X * PowerSeries.C (ε⁻¹).val)
          (PowerSeries.X ^ 2) := by
  letI : TopologicalSpace BivariateSeries := piTop
  letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
  have h0 : Multipliable (fun n => 1 - q ^ 2 * (q ^ 2) ^ n) :=
    multipliable_factors
  have h1 : Multipliable (fun n => 1 - (-q * a) * (q ^ 2) ^ n) :=
    (factors_multipliable a).congr (fun n => by ring)
  have h2 : Multipliable (fun n => 1 - (-q * aI) * (q ^ 2) ^ n) :=
    (factors_multipliable aI).congr (fun n => by ring)
  unfold lhs
  rw [map_mul, map_mul,
    jacobiUnitReceiver_qPochhammerInf ε _ _ h0,
    jacobiUnitReceiver_qPochhammerInf ε _ _ h1,
    jacobiUnitReceiver_qPochhammerInf ε _ _ h2]
  simp

/-- The complete signed square theta series returned by the unit receiver.
Its coefficient is defined from the already checked Jacobi source coefficient,
so no analytic summation or convergence chart is introduced. -/
def unitSquareTheta (ε : ℤˣ) : IntegerSeries :=
  PowerSeries.mk fun n =>
    laurentUnitReceiver ε (PowerSeries.coeff n rhs)

@[simp] theorem coeff_unitSquareTheta (ε : ℤˣ) (n : ℕ) :
    PowerSeries.coeff n (unitSquareTheta ε) =
      laurentUnitReceiver ε (PowerSeries.coeff n rhs) := by
  simp [unitSquareTheta]

/-- Evaluating the Laurent coordinate of the Jacobi source returns the exact
signed square theta series. -/
theorem jacobiUnitReceiver_rhs (ε : ℤˣ) :
    jacobiUnitReceiver ε rhs = unitSquareTheta ε := by
  apply PowerSeries.ext
  intro n
  simp

/-- The checked Jacobi equality commutes with every unit specialization. -/
theorem jacobi_triple_product_unit_specialization (ε : ℤˣ) :
    jacobiUnitReceiver ε lhs = unitSquareTheta ε := by
  rw [← jacobiUnitReceiver_rhs ε]
  exact congrArg (jacobiUnitReceiver ε) jacobi_triple_product

/-- The product and population faces of every integer-unit specialization
are exactly the same complete power series. -/
theorem jacobi_unit_product_eq_unitSquareTheta (ε : ℤˣ) :
    letI : TopologicalSpace IntegerSeries := integerSeriesPiTop
    qPochhammerInf (PowerSeries.X ^ 2) (PowerSeries.X ^ 2) *
        qPochhammerInf (-PowerSeries.X * PowerSeries.C ε.val)
          (PowerSeries.X ^ 2) *
        qPochhammerInf (-PowerSeries.X * PowerSeries.C (ε⁻¹).val)
          (PowerSeries.X ^ 2) =
      unitSquareTheta ε := by
  rw [← jacobiUnitReceiver_lhs ε,
    jacobi_triple_product_unit_specialization]

#print axioms jacobiUnitReceiver_rhs
#print axioms jacobiUnitReceiver_qPochhammerInf
#print axioms jacobiUnitReceiver_lhs
#print axioms jacobi_triple_product_unit_specialization
#print axioms jacobi_unit_product_eq_unitSquareTheta

end Soma.Holonics.Mathematics.JacobiUnitSpecialization
