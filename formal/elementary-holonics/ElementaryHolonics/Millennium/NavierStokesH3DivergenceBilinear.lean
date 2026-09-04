import ElementaryHolonics.Millennium.NavierStokesH3Bilinear

/-!
# The divergence-form periodic `H³ × H³ → H²` Fourier passage

The predecessor proves the genuine three-dimensional lattice summability and closes scalar
Fourier multiplication on the complete `H³` coefficient carrier.  This owner spends exactly one
derivative: the multiplier `2π i k_j` maps `H³` into `H²`.  Finite component assembly then returns

`(u, v) ↦ (∑ j, ∂j (u_j v_a))_a`

as an honest vector of complete `H²(ℤ³)` coefficient populations, with its exact infinite
coefficient law.  No cutoff, local-existence premise, Duhamel conclusion, or fixed-point wrapper is
introduced.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesH3Bilinear

/-! ## Spending one exact Sobolev order -/

/-- [proved-derived] The order-two weight times one coordinate derivative symbol is bounded by
the order-three weight at the same addressed frequency. -/
theorem periodicSobolevWeight_two_mul_coordinate_symbol_sq_le_three
    (coordinate : Fin 3) (k : SpatialFrequency) :
    periodicSobolevWeight 2 k *
        ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) ≤
      periodicSobolevWeight 3 k := by
  have hcoordinate : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ coordinate)
  have hsymbol :
      (2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2 ≤ torusStokesEigenvalue k := by
    rw [torusStokesEigenvalue]
    exact mul_le_mul_of_nonneg_left hcoordinate (sq_nonneg (2 * Real.pi))
  have hbase : 0 ≤ 1 + torusStokesEigenvalue k :=
    add_nonneg zero_le_one (torusStokesEigenvalue_nonneg k)
  rw [periodicSobolevWeight, periodicSobolevWeight]
  calc
    (1 + torusStokesEigenvalue k) ^ 2 *
        ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) ≤
        (1 + torusStokesEigenvalue k) ^ 2 * torusStokesEigenvalue k :=
      mul_le_mul_of_nonneg_left hsymbol (sq_nonneg _)
    _ ≤ (1 + torusStokesEigenvalue k) ^ 2 *
        (1 + torusStokesEigenvalue k) :=
      mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left zero_le_one) (sq_nonneg _)
    _ = (1 + torusStokesEigenvalue k) ^ 3 := by ring

private theorem norm_periodicSobolevThreeDerivative_sq
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3)
    (k : SpatialFrequency) :
    ‖periodicSobolevThreeDerivative coordinate coeff k‖ ^ 2 =
      ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2 := by
  rw [periodicSobolevThreeDerivative_apply]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
    Complex.norm_I, Complex.norm_intCast, mul_one]
  rw [abs_of_pos Real.pi_pos]
  ring_nf
  rw [sq_abs]
  ring

/-- [definition] A coordinate derivative of an `H³` population, returned with its genuine
order-two Sobolev witness rather than merely in the underlying Fourier `ℓ²` carrier. -/
def periodicSobolevThreeDerivativeIntoTwo
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3) :
    PeriodicSobolevCoefficients 2 :=
  ⟨periodicSobolevThreeDerivative coordinate coeff, by
    unfold HasPeriodicSobolevCoefficients
    refine Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg 2 k) (sq_nonneg _))
      (fun k ↦ ?_) coeff.2
    rw [norm_periodicSobolevThreeDerivative_sq]
    calc
      periodicSobolevWeight 2 k *
          (((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2) =
          (periodicSobolevWeight 2 k *
            ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2)) * ‖coeff.1 k‖ ^ 2 := by
        ring
      _ ≤ periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (periodicSobolevWeight_two_mul_coordinate_symbol_sq_le_three coordinate k)
          (sq_nonneg _)⟩

@[simp]
theorem periodicSobolevThreeDerivativeIntoTwo_apply
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3)
    (k : SpatialFrequency) :
    (periodicSobolevThreeDerivativeIntoTwo coordinate coeff).1 k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k :=
  rfl

/-! ## Finite assembly preserves weighted membership -/

private theorem hasPeriodicSobolevCoefficients_zero (order : ℕ) :
    HasPeriodicSobolevCoefficients order (0 : PeriodicFourierL2) := by
  unfold HasPeriodicSobolevCoefficients
  simpa using (summable_zero : Summable fun _ : SpatialFrequency ↦ (0 : ℝ))

private theorem hasPeriodicSobolevCoefficients_add
    {order : ℕ} {left right : PeriodicFourierL2}
    (hleft : HasPeriodicSobolevCoefficients order left)
    (hright : HasPeriodicSobolevCoefficients order right) :
    HasPeriodicSobolevCoefficients order (left + right) := by
  unfold HasPeriodicSobolevCoefficients at hleft hright ⊢
  have hbound : Summable fun k ↦ 2 *
      (periodicSobolevWeight order k * ‖left k‖ ^ 2 +
        periodicSobolevWeight order k * ‖right k‖ ^ 2) :=
    (hleft.add hright).mul_left 2
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg order k) (sq_nonneg _))
    (fun k ↦ ?_) hbound
  simp only [lp.coeFn_add, Pi.add_apply]
  have hnorm := norm_add_le (left k) (right k)
  have hsquare : ‖left k + right k‖ ^ 2 ≤ (‖left k‖ + ‖right k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hweight := periodicSobolevWeight_nonneg order k
  calc
    periodicSobolevWeight order k * ‖left k + right k‖ ^ 2 ≤
        periodicSobolevWeight order k * (‖left k‖ + ‖right k‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hweight
    _ ≤ 2 *
        (periodicSobolevWeight order k * ‖left k‖ ^ 2 +
          periodicSobolevWeight order k * ‖right k‖ ^ 2) := by
      nlinarith [mul_nonneg hweight (sq_nonneg (‖left k‖ - ‖right k‖))]

private theorem hasPeriodicSobolevCoefficients_finset_sum
    {order : ℕ} {ι : Type*} (s : Finset ι) (coeff : ι → PeriodicFourierL2)
    (hcoeff : ∀ i ∈ s, HasPeriodicSobolevCoefficients order (coeff i)) :
    HasPeriodicSobolevCoefficients order (∑ i ∈ s, coeff i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasPeriodicSobolevCoefficients_zero order
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact hasPeriodicSobolevCoefficients_add (hcoeff i (Finset.mem_insert_self i s))
        (ih (fun j hj ↦ hcoeff j (Finset.mem_insert_of_mem hj)))

/-! ## The exact divergence-form bilinear population -/

/-- [definition] One addressed divergence face `∂j(left · right)` in the `H²` carrier. -/
def scalarH3DivergenceProduct
    (coordinate : Fin 3) (left right : PeriodicSobolevCoefficients 3) :
    PeriodicSobolevCoefficients 2 :=
  periodicSobolevThreeDerivativeIntoTwo coordinate (scalarH3Product left right)

@[simp]
theorem scalarH3DivergenceProduct_apply
    (coordinate : Fin 3) (left right : PeriodicSobolevCoefficients 3)
    (k : SpatialFrequency) :
    (scalarH3DivergenceProduct coordinate left right).1 k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p, left.1 p * right.1 (k - p)) := by
  rw [scalarH3DivergenceProduct, periodicSobolevThreeDerivativeIntoTwo_apply,
    scalarH3Product_apply]

/-- [definition] The complete coefficient population of
`∑ j, ∂j (advecting_j · transported_output)`, returned in `H²`. -/
def h3DivergenceConvolutionComponent
    (advecting transported : PeriodicVectorSobolevThree) (output : Fin 3) :
    PeriodicSobolevCoefficients 2 :=
  ⟨∑ coordinate : Fin 3,
      (scalarH3DivergenceProduct coordinate (advecting coordinate)
        (transported output)).1,
    hasPeriodicSobolevCoefficients_finset_sum Finset.univ
      (fun coordinate ↦
        (scalarH3DivergenceProduct coordinate (advecting coordinate)
          (transported output)).1)
      (fun coordinate _ ↦
        (scalarH3DivergenceProduct coordinate (advecting coordinate)
          (transported output)).2)⟩

/-- [definition] The three output components of the divergence-form quadratic passage. -/
def h3DivergenceConvolution
    (advecting transported : PeriodicVectorSobolevThree) :
    Fin 3 → PeriodicSobolevCoefficients 2 :=
  fun output ↦ h3DivergenceConvolutionComponent advecting transported output

/-- [proved-derived] Exact complete-lattice coefficient law for the divergence-form passage. -/
theorem h3DivergenceConvolution_apply
    (advecting transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution advecting transported output).1 k =
      ∑ coordinate : Fin 3,
        (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
          (∑' p, (advecting coordinate).1 p *
            (transported output).1 (k - p)) := by
  change (∑ coordinate : Fin 3,
    (scalarH3DivergenceProduct coordinate (advecting coordinate)
      (transported output)).1) k = _
  simp only [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact scalarH3DivergenceProduct_apply coordinate
    (advecting coordinate) (transported output) k

#print axioms periodicSobolevWeight_two_mul_coordinate_symbol_sq_le_three
#print axioms periodicSobolevThreeDerivativeIntoTwo
#print axioms scalarH3DivergenceProduct_apply
#print axioms h3DivergenceConvolution_apply

end Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
