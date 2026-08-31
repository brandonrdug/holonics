import ElementaryHolonics.Mathematics.JacobiFiniteDiagonalProduct
import ElementaryHolonics.Mathematics.JacobiUnitSpecialization

/-!
# Exact coefficient stabilization of the Jacobi Euler cube

The finite diagonal derivative of the Jacobi product returns

`E_(N+1)^2 E_N`.

This file proves that every coefficient below the factor aperture `N` is
already exactly its coefficient in the completed Euler cube `E^3`.  The
passage is coefficientwise finite: no approximation, limiting estimate, or
analytic diagonal substitution is used.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.JacobiEulerCubeStabilization

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiUnitSpecialization
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalProduct

open scoped PowerSeries.WithPiTopology

/-- The completed even Euler population returned by the diagonal
specialization. -/
def infiniteEvenEulerProduct : PowerSeries ℤ :=
  qPochhammerInf (PowerSeries.X ^ 2) (PowerSeries.X ^ 2)

/-- Its first `N` addressed factors. -/
def finiteEvenEulerSeries (N : ℕ) : PowerSeries ℤ :=
  qPoch (PowerSeries.X ^ 2) (PowerSeries.X ^ 2) N

/-- Below the first omitted factor, the finite and complete Euler populations
have exactly the same coefficient.  The proof transports the already checked
bivariate stabilization theorem through the continuous unit receiver. -/
theorem coeff_infiniteEvenEulerProduct_eq_finite
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d infiniteEvenEulerProduct =
      PowerSeries.coeff d (finiteEvenEulerSeries N) := by
  letI : TopologicalSpace R := piTop
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have hmult : Multipliable (fun n => 1 - q ^ 2 * (q ^ 2) ^ n) :=
    multipliable_factors
  have hmapInf := jacobiUnitReceiver_qPochhammerInf (1 : ℤˣ)
    (q ^ 2) (q ^ 2) hmult
  have hstable :
      PowerSeries.coeff d
          (qPochhammerInf (q ^ 2) (q ^ 2) : R) =
        PowerSeries.coeff d (qPoch (q ^ 2) (q ^ 2) N : R) := by
    simpa [pow_two] using lhs_coeff_stable (-q) d N h
  have hfiniteMap :
      jacobiUnitReceiver (1 : ℤˣ) (qPoch (q ^ 2) (q ^ 2) N) =
        finiteEvenEulerSeries N := by
    rw [map_qPoch]
    simp [finiteEvenEulerSeries]
  calc
    PowerSeries.coeff d infiniteEvenEulerProduct =
        PowerSeries.coeff d
          (jacobiUnitReceiver (1 : ℤˣ)
            (qPochhammerInf (q ^ 2) (q ^ 2))) := by
              rw [hmapInf]
              simp only [jacobiUnitReceiver, PowerSeries.map_X, map_pow]
              rfl
    _ = laurentUnitReceiver (1 : ℤˣ)
          (PowerSeries.coeff d
            (qPochhammerInf (q ^ 2) (q ^ 2))) := by simp
    _ = laurentUnitReceiver (1 : ℤˣ)
          (PowerSeries.coeff d (qPoch (q ^ 2) (q ^ 2) N)) := by
            rw [hstable]
    _ = PowerSeries.coeff d
          (jacobiUnitReceiver (1 : ℤˣ)
            (qPoch (q ^ 2) (q ^ 2) N)) := by simp
    _ = PowerSeries.coeff d (finiteEvenEulerSeries N) := by
      rw [hfiniteMap]

/-- Coefficient equality through one addressed degree is preserved by one
finite Cauchy-product layer. -/
theorem coeff_mul_eq_of_coeff_le
    (F F' G G' : PowerSeries ℤ) (d : ℕ)
    (hF : ∀ j ≤ d, PowerSeries.coeff j F = PowerSeries.coeff j F')
    (hG : ∀ j ≤ d, PowerSeries.coeff j G = PowerSeries.coeff j G') :
    PowerSeries.coeff d (F * G) = PowerSeries.coeff d (F' * G') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum : p.1 + p.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [hF p.1 (by omega), hG p.2 (by omega)]

/-- The completed cube, written in the same multiplication association as
the finite diagonal return. -/
def infiniteEvenEulerCube : PowerSeries ℤ :=
  infiniteEvenEulerProduct ^ 2 * infiniteEvenEulerProduct

/-- The exact finite body returned by differentiating after the diagonal
specialization `a = -q`. -/
def finiteNeighborEulerReturn (N : ℕ) : PowerSeries ℤ :=
  finiteEvenEulerSeries (N + 1) ^ 2 * finiteEvenEulerSeries N

/-- **EXACT FINITE-TO-COMPLETE RETURN.**  Every coefficient below the finite
factor aperture has already returned its completed Euler-cube value. -/
theorem coeff_infiniteEvenEulerCube_eq_finiteNeighbor
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d infiniteEvenEulerCube =
      PowerSeries.coeff d (finiteNeighborEulerReturn N) := by
  have hN : ∀ j ≤ d,
      PowerSeries.coeff j infiniteEvenEulerProduct =
        PowerSeries.coeff j (finiteEvenEulerSeries N) := by
    intro j hj
    exact coeff_infiniteEvenEulerProduct_eq_finite j N (by omega)
  have hN1 : ∀ j ≤ d,
      PowerSeries.coeff j infiniteEvenEulerProduct =
        PowerSeries.coeff j (finiteEvenEulerSeries (N + 1)) := by
    intro j hj
    exact coeff_infiniteEvenEulerProduct_eq_finite j (N + 1) (by omega)
  have hSquares : ∀ j ≤ d,
      PowerSeries.coeff j (infiniteEvenEulerProduct ^ 2) =
        PowerSeries.coeff j (finiteEvenEulerSeries (N + 1) ^ 2) := by
    intro j hj
    rw [pow_two, pow_two]
    exact coeff_mul_eq_of_coeff_le _ _ _ _ j
      (fun k hk => hN1 k (le_trans hk hj))
      (fun k hk => hN1 k (le_trans hk hj))
  unfold infiniteEvenEulerCube finiteNeighborEulerReturn
  exact coeff_mul_eq_of_coeff_le _ _ _ _ d hSquares hN

#print axioms coeff_infiniteEvenEulerProduct_eq_finite
#print axioms coeff_infiniteEvenEulerCube_eq_finiteNeighbor

end Soma.Holonics.Mathematics.JacobiEulerCubeStabilization
