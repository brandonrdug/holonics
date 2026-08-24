import ElementaryHolonics.Millennium.NavierStokesCoordinateH3FullEstimate
import ElementaryHolonics.Millennium.NavierStokesTorusCubeIntegral
import ElementaryHolonics.Millennium.NavierStokesWeightedSobolevHilbert

/-!
# Smooth periodic slices enter the complete weighted H³ carrier

This owner binds the actual Fourier coefficients of a smooth one-periodic velocity slice to
Mathlib's complete Fourier Hilbert carrier.  Parseval keeps every component and every ordered
coordinate derivative face.  The eventual weighted estimate uses the exact unit-torus multiplier
`2π i k_j`; no finite frequency cutoff or independently supplied coefficient population occurs.
-/

noncomputable section

open ContDiff MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FullEstimate
open Soma.Holonics.Millennium.NavierStokesCoordinateH3MiddleRedistribution
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The actual coefficient population and Parseval -/

/-- One component of a smooth periodic slice descended to the genuine quotient torus. -/
def smoothSliceComponentLift
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) : C(SpatialTorus, ℂ) :=
  periodicTorusLift (complexVelocityComponent u component)
    (continuous_complexVelocityComponent hu.continuous component)
    (isOnePeriodic_complexVelocityComponent hperiodic component)

/-- The actual scalar Fourier coefficient population, packaged in Mathlib's complete `ℓ2`.
The proof arguments only certify descent and do not alter the returned coefficients. -/
def smoothSliceFourierL2
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) : PeriodicFourierL2 :=
  periodicFourierRepresentation
    ((smoothSliceComponentLift u hu hperiodic component).toLp 2 volume ℂ)

@[simp]
theorem smoothSliceFourierL2_apply
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) :
    smoothSliceFourierL2 u hu hperiodic component k =
      vectorSpatialFourierCoeff u hu.continuous hperiodic k component := by
  rw [smoothSliceFourierL2, periodicFourierRepresentation_apply,
    UnitAddTorus.mFourierCoeff_toLp, vectorSpatialFourierCoeff_apply]
  rfl

/-- Parseval for the actual component receiver, before any derivative weight is introduced. -/
theorem hasSum_sq_smoothSliceFourierL2
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    HasSum (fun k ↦ ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2)
      (∫ q : SpatialTorus,
        ‖smoothSliceComponentLift u hu hperiodic component q‖ ^ 2) := by
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff
    ((smoothSliceComponentLift u hu hperiodic component).toLp 2 volume ℂ)
  have hintegral :
      (∫ q : SpatialTorus,
          ‖((smoothSliceComponentLift u hu hperiodic component).toLp 2 volume ℂ) q‖ ^ 2) =
        ∫ q : SpatialTorus,
          ‖smoothSliceComponentLift u hu hperiodic component q‖ ^ 2 := by
    have hcoe :
        ((smoothSliceComponentLift u hu hperiodic component).toLp 2 volume ℂ :
            SpatialTorus → ℂ) =ᵐ[volume]
          smoothSliceComponentLift u hu hperiodic component :=
      (smoothSliceComponentLift u hu hperiodic component).coeFn_toLp volume
    apply integral_congr_ae
    filter_upwards [hcoe] with q hq
    exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hq
  rw [← hintegral]
  refine HasSum.congr_fun h (fun k ↦ ?_)
  apply congrArg (fun z : ℂ ↦ ‖z‖ ^ 2)
  exact periodicFourierRepresentation_apply
    ((smoothSliceComponentLift u hu hperiodic component).toLp 2 volume ℂ) k

/-! ## Exact coordinate multipliers -/

/-- The Fourier receiver of one actual spatial coordinate derivative is the exact unit-torus
multiplier of the source receiver. -/
theorem smoothSliceFourierL2_spatialDirectionalJet
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (coordinate component : Fin 3) (k : SpatialFrequency) :
    smoothSliceFourierL2 (spatialDirectionalJet u coordinate)
        (spatialDirectionalJet_contDiff u hu coordinate)
        (spatialDirectionalJet_isOnePeriodic u hperiodic coordinate) component k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        smoothSliceFourierL2 u hu hperiodic component k := by
  rw [smoothSliceFourierL2_apply, smoothSliceFourierL2_apply]
  have hmode := actualJacobianFourierMode_eq_multiplier
    u (hu.of_le (by norm_num)) hperiodic k component coordinate
  rw [actualJacobianFourierMode] at hmode
  rw [vectorSpatialFourierCoeff_apply]
  convert hmode using 1
  apply congrArg (fun field : C(SpatialTorus, ℂ) ↦
    torusSpatialFourierCoeff field k)
  ext q
  obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_surjective q
  simp only [periodicTorusLift_projection]
  change ((fderiv ℝ u x (spatialBasisVector coordinate)) component : ℂ) =
    (velocityJacobianAt u x component coordinate : ℂ)
  simp [velocityJacobianAt, jacobianMatrix_apply, spatialBasisVector]

/-! ## The complete ordered multiplier population -/

/-- One coordinate's nonnegative contribution to the Stokes eigenvalue. -/
def coordinateStokesEigenvalue (coordinate : Fin 3) (k : SpatialFrequency) : ℝ :=
  (2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2

theorem coordinateStokesEigenvalue_nonneg
    (coordinate : Fin 3) (k : SpatialFrequency) :
    0 ≤ coordinateStokesEigenvalue coordinate k := by
  unfold coordinateStokesEigenvalue
  positivity

/-- The Stokes eigenvalue is exactly the sum of its three addressed coordinate faces. -/
theorem torusStokesEigenvalue_eq_sum_coordinate
    (k : SpatialFrequency) :
    torusStokesEigenvalue k =
      ∑ coordinate : Fin 3, coordinateStokesEigenvalue coordinate k := by
  unfold torusStokesEigenvalue coordinateStokesEigenvalue frequencySquared
  rw [Finset.mul_sum]

private theorem norm_coordinateMultiplier_sq
    (coordinate : Fin 3) (k : SpatialFrequency) :
    ‖2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)‖ ^ 2 =
      coordinateStokesEigenvalue coordinate k := by
  simp [coordinateStokesEigenvalue, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_pos.le]
  rw [mul_pow, sq_abs]

/-- Squared coefficients of every first ordered coordinate face. -/
theorem norm_sq_smoothSliceFourierL2_first
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (coordinate component : Fin 3) (k : SpatialFrequency) :
    ‖smoothSliceFourierL2 (spatialDirectionalJet u coordinate)
        (spatialDirectionalJet_contDiff u hu coordinate)
        (spatialDirectionalJet_isOnePeriodic u hperiodic coordinate) component k‖ ^ 2 =
      coordinateStokesEigenvalue coordinate k *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  rw [smoothSliceFourierL2_spatialDirectionalJet, norm_mul, mul_pow,
    norm_coordinateMultiplier_sq]

/-- Squared coefficients of every ordered second coordinate word. -/
theorem norm_sq_smoothSliceFourierL2_second
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (i j component : Fin 3) (k : SpatialFrequency) :
    ‖smoothSliceFourierL2 (secondSpatialCoordinateJet u i j)
        (secondSpatialCoordinateJet_contDiff u hu i j)
        (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component k‖ ^ 2 =
      coordinateStokesEigenvalue i k * coordinateStokesEigenvalue j k *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  calc
    _ = coordinateStokesEigenvalue i k *
        ‖smoothSliceFourierL2 (spatialDirectionalJet u j)
          (spatialDirectionalJet_contDiff u hu j)
          (spatialDirectionalJet_isOnePeriodic u hperiodic j) component k‖ ^ 2 :=
      norm_sq_smoothSliceFourierL2_first
        (spatialDirectionalJet u j) (spatialDirectionalJet_contDiff u hu j)
        (spatialDirectionalJet_isOnePeriodic u hperiodic j) i component k
    _ = _ := by
      rw [norm_sq_smoothSliceFourierL2_first u hu hperiodic j component k]
      ring

/-- Squared coefficients of every ordered third coordinate word. -/
theorem norm_sq_smoothSliceFourierL2_third
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (i j l component : Fin 3) (k : SpatialFrequency) :
    ‖smoothSliceFourierL2 (thirdSpatialCoordinateJet u i j l)
        (thirdSpatialCoordinateJet_contDiff u hu i j l)
        (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component k‖ ^ 2 =
      coordinateStokesEigenvalue i k * coordinateStokesEigenvalue j k *
        coordinateStokesEigenvalue l k *
          ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  calc
    _ = coordinateStokesEigenvalue i k *
        ‖smoothSliceFourierL2 (secondSpatialCoordinateJet u j l)
          (secondSpatialCoordinateJet_contDiff u hu j l)
          (secondSpatialCoordinateJet_isOnePeriodic u hperiodic j l) component k‖ ^ 2 :=
      norm_sq_smoothSliceFourierL2_first
        (secondSpatialCoordinateJet u j l) (secondSpatialCoordinateJet_contDiff u hu j l)
        (secondSpatialCoordinateJet_isOnePeriodic u hperiodic j l) i component k
    _ = _ := by
      rw [norm_sq_smoothSliceFourierL2_second u hu hperiodic j l component k]
      ring

private theorem sum_pair_product_eq_sq (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, a i * a j) = (∑ i : Fin 3, a i) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]

private theorem sum_triple_product_eq_cube (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, a i * a j * a l) =
      (∑ i : Fin 3, a i) ^ 3 := by
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, a i * a j * a l) =
        ∑ i : Fin 3, ∑ j : Fin 3, (a i * a j) * (∑ l : Fin 3, a l) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
    _ = (∑ i : Fin 3, ∑ j : Fin 3, a i * a j) * (∑ l : Fin 3, a l) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_mul]
    _ = _ := by
      rw [sum_pair_product_eq_sq]
      ring

/-- Summing every ordered first word returns the first Stokes power. -/
theorem sum_norm_sq_smoothSliceFourierL2_first
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) :
    (∑ i : Fin 3,
        ‖smoothSliceFourierL2 (spatialDirectionalJet u i)
          (spatialDirectionalJet_contDiff u hu i)
          (spatialDirectionalJet_isOnePeriodic u hperiodic i) component k‖ ^ 2) =
      torusStokesEigenvalue k *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  simp_rw [norm_sq_smoothSliceFourierL2_first
    (u := u) (hu := hu) (hperiodic := hperiodic)]
  rw [← Finset.sum_mul, ← torusStokesEigenvalue_eq_sum_coordinate]

/-- Summing all nine ordered second words returns the square of the Stokes eigenvalue. -/
theorem sum_norm_sq_smoothSliceFourierL2_second
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        ‖smoothSliceFourierL2 (secondSpatialCoordinateJet u i j)
          (secondSpatialCoordinateJet_contDiff u hu i j)
          (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component k‖ ^ 2) =
      torusStokesEigenvalue k ^ 2 *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  simp_rw [norm_sq_smoothSliceFourierL2_second
    (u := u) (hu := hu) (hperiodic := hperiodic)]
  let a : Fin 3 → ℝ := fun i ↦ coordinateStokesEigenvalue i k
  let b : ℝ := ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
        coordinateStokesEigenvalue i k * coordinateStokesEigenvalue j k * b) =
        (∑ i : Fin 3, ∑ j : Fin 3, a i * a j) * b := by
      simp only [a]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_mul]
    _ = (∑ i : Fin 3, a i) ^ 2 * b := by rw [sum_pair_product_eq_sq]
    _ = torusStokesEigenvalue k ^ 2 * b := by
      rw [torusStokesEigenvalue_eq_sum_coordinate]

/-- Summing all twenty-seven ordered third words returns the cube of the Stokes eigenvalue. -/
theorem sum_norm_sq_smoothSliceFourierL2_third
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ‖smoothSliceFourierL2 (thirdSpatialCoordinateJet u i j l)
          (thirdSpatialCoordinateJet_contDiff u hu i j l)
          (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component k‖ ^ 2) =
      torusStokesEigenvalue k ^ 3 *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  simp_rw [norm_sq_smoothSliceFourierL2_third
    (u := u) (hu := hu) (hperiodic := hperiodic)]
  let a : Fin 3 → ℝ := fun i ↦ coordinateStokesEigenvalue i k
  let b : ℝ := ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        coordinateStokesEigenvalue i k * coordinateStokesEigenvalue j k *
          coordinateStokesEigenvalue l k * b) =
        (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, a i * a j * a l) * b := by
      simp only [a]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul]
    _ = (∑ i : Fin 3, a i) ^ 3 * b := by rw [sum_triple_product_eq_cube]
    _ = torusStokesEigenvalue k ^ 3 * b := by
      rw [torusStokesEigenvalue_eq_sum_coordinate]

/-- The only polynomial loss in passing from the inhomogeneous H³ weight to the complete
ordered derivative population. -/
theorem periodicSobolevWeight_three_le_derivativePolynomial
    (k : SpatialFrequency) :
    periodicSobolevWeight 3 k ≤
      3 * (1 + torusStokesEigenvalue k + torusStokesEigenvalue k ^ 2 +
        torusStokesEigenvalue k ^ 3) := by
  have heigen : 0 ≤ torusStokesEigenvalue k := torusStokesEigenvalue_nonneg k
  unfold periodicSobolevWeight
  nlinarith [mul_nonneg (sq_nonneg (torusStokesEigenvalue k)) heigen]

/-! ## Entry into the complete H³ carrier -/

/-- The complete `1 + 3 + 9 + 27` squared-coefficient population for one velocity component. -/
def smoothSliceDerivativeSquarePopulation
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) : ℝ :=
  ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 +
    (∑ i : Fin 3,
      ‖smoothSliceFourierL2 (spatialDirectionalJet u i)
        (spatialDirectionalJet_contDiff u hu i)
        (spatialDirectionalJet_isOnePeriodic u hperiodic i) component k‖ ^ 2) +
    (∑ i : Fin 3, ∑ j : Fin 3,
      ‖smoothSliceFourierL2 (secondSpatialCoordinateJet u i j)
        (secondSpatialCoordinateJet_contDiff u hu i j)
        (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component k‖ ^ 2) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      ‖smoothSliceFourierL2 (thirdSpatialCoordinateJet u i j l)
        (thirdSpatialCoordinateJet_contDiff u hu i j l)
        (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component k‖ ^ 2)

theorem smoothSliceDerivativeSquarePopulation_nonneg
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) :
    0 ≤ smoothSliceDerivativeSquarePopulation u hu hperiodic component k := by
  unfold smoothSliceDerivativeSquarePopulation
  positivity

/-- Pointwise, the weighted H³ receiver factors through the complete ordered derivative
population with the explicit polynomial constant three. -/
theorem periodicSobolevWeight_three_mul_norm_sq_le_population
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) :
    periodicSobolevWeight 3 k *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 ≤
      3 * smoothSliceDerivativeSquarePopulation u hu hperiodic component k := by
  let b : ℝ := ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2
  have hb : 0 ≤ b := sq_nonneg _
  have hweight := mul_le_mul_of_nonneg_right
    (periodicSobolevWeight_three_le_derivativePolynomial k) hb
  calc
    periodicSobolevWeight 3 k * b ≤
        (3 * (1 + torusStokesEigenvalue k + torusStokesEigenvalue k ^ 2 +
          torusStokesEigenvalue k ^ 3)) * b := hweight
    _ = 3 * smoothSliceDerivativeSquarePopulation u hu hperiodic component k := by
      unfold smoothSliceDerivativeSquarePopulation
      rw [sum_norm_sq_smoothSliceFourierL2_first u hu hperiodic component k,
        sum_norm_sq_smoothSliceFourierL2_second u hu hperiodic component k,
        sum_norm_sq_smoothSliceFourierL2_third u hu hperiodic component k]
      dsimp [b]
      ring

/-- Parseval makes the full ordered derivative population summable over every frequency. -/
theorem summable_smoothSliceDerivativeSquarePopulation
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    Summable (smoothSliceDerivativeSquarePopulation u hu hperiodic component) := by
  have hzero : Summable (fun k ↦
      ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2) :=
    (hasSum_sq_smoothSliceFourierL2 u hu hperiodic component).summable
  have hone : Summable (fun k ↦ ∑ i : Fin 3,
      ‖smoothSliceFourierL2 (spatialDirectionalJet u i)
        (spatialDirectionalJet_contDiff u hu i)
        (spatialDirectionalJet_isOnePeriodic u hperiodic i) component k‖ ^ 2) := by
    apply summable_sum
    intro i _hi
    exact (hasSum_sq_smoothSliceFourierL2 (spatialDirectionalJet u i)
      (spatialDirectionalJet_contDiff u hu i)
      (spatialDirectionalJet_isOnePeriodic u hperiodic i) component).summable
  have htwo : Summable (fun k ↦ ∑ i : Fin 3, ∑ j : Fin 3,
      ‖smoothSliceFourierL2 (secondSpatialCoordinateJet u i j)
        (secondSpatialCoordinateJet_contDiff u hu i j)
        (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component k‖ ^ 2) := by
    apply summable_sum
    intro i _hi
    apply summable_sum
    intro j _hj
    exact (hasSum_sq_smoothSliceFourierL2 (secondSpatialCoordinateJet u i j)
      (secondSpatialCoordinateJet_contDiff u hu i j)
      (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component).summable
  have hthree : Summable (fun k ↦ ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      ‖smoothSliceFourierL2 (thirdSpatialCoordinateJet u i j l)
        (thirdSpatialCoordinateJet_contDiff u hu i j l)
        (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component k‖ ^ 2) := by
    apply summable_sum
    intro i _hi
    apply summable_sum
    intro j _hj
    apply summable_sum
    intro l _hl
    exact (hasSum_sq_smoothSliceFourierL2 (thirdSpatialCoordinateJet u i j l)
      (thirdSpatialCoordinateJet_contDiff u hu i j l)
      (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component).summable
  exact ((hzero.add hone).add htwo).add hthree

/-- The actual coefficient population of every smooth periodic component has Sobolev order three. -/
theorem hasPeriodicSobolevCoefficients_three_smoothSlice
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    HasPeriodicSobolevCoefficients 3
      (smoothSliceFourierL2 u hu hperiodic component) := by
  unfold HasPeriodicSobolevCoefficients
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg 3 k) (sq_nonneg _))
    (fun k ↦ periodicSobolevWeight_three_mul_norm_sq_le_population
      u hu hperiodic component k)
    ((summable_smoothSliceDerivativeSquarePopulation u hu hperiodic component).mul_left 3)

/-- The old coefficient subtype, carrying the actual unweighted Fourier population. -/
def smoothSliceSobolevCoefficients
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) : PeriodicSobolevCoefficients 3 :=
  ⟨smoothSliceFourierL2 u hu hperiodic component,
    hasPeriodicSobolevCoefficients_three_smoothSlice u hu hperiodic component⟩

/-- The actual component in the complete native weighted H³ Hilbert carrier. -/
def smoothSliceWeightedH3Component
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) : PeriodicWeightedSobolev 3 :=
  coefficientWeightedRealization 3
    (smoothSliceSobolevCoefficients u hu hperiodic component)

/-- All three component-addressed actual coefficient populations in complete weighted H³. -/
def smoothSliceVectorWeightedH3
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u) :
    PeriodicVectorWeightedSobolev 3 :=
  fun component ↦ smoothSliceWeightedH3Component u hu hperiodic component

/-- Unweighting the native carrier returns exactly the actual Fourier coefficient population. -/
theorem weightedSobolevCoefficients_smoothSliceWeightedH3Component
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    weightedSobolevCoefficients 3
        (smoothSliceWeightedH3Component u hu hperiodic component) =
      smoothSliceSobolevCoefficients u hu hperiodic component := by
  exact weightedSobolevCoefficients_coefficientWeightedRealization 3 _

/-- Coefficientwise, native unweighting is the original field's actual genuine-torus Fourier
receiver. -/
theorem unweighted_smoothSliceVectorWeightedH3_apply
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3
        (smoothSliceVectorWeightedH3 u hu hperiodic component)).1 k =
      vectorSpatialFourierCoeff u hu.continuous hperiodic k component := by
  rw [smoothSliceVectorWeightedH3,
    weightedSobolevCoefficients_smoothSliceWeightedH3Component]
  exact smoothSliceFourierL2_apply u hu hperiodic component k

/-! ## Parseval transported back to the coordinate energy chart -/

/-- Parseval and the exact cube--torus chart transport identify one component's complete
coefficient square population with its actual Euclidean unit-cube square integral. -/
theorem tsum_sq_smoothSliceFourierL2_eq_integral_unitCube
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    (∑' k, ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2) =
      ∫ x in unitCube, (u x component) ^ 2 := by
  let squareLift : C(SpatialTorus, ℝ) := {
    toFun := fun q ↦ ‖smoothSliceComponentLift u hu hperiodic component q‖ ^ 2
    continuous_toFun :=
      (smoothSliceComponentLift u hu hperiodic component).continuous.norm.pow 2 }
  have hparseval :=
    (hasSum_sq_smoothSliceFourierL2 u hu hperiodic component).tsum_eq
  have hchart := integral_euclideanToSpatialTorus_unitCube squareLift
  calc
    (∑' k, ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2) =
        ∫ q : SpatialTorus,
          ‖smoothSliceComponentLift u hu hperiodic component q‖ ^ 2 := hparseval
    _ = ∫ x in unitCube, squareLift (euclideanToSpatialTorus x) := by
      simpa [squareLift] using hchart.symm
    _ = ∫ x in unitCube, (u x component) ^ 2 := by
      apply setIntegral_congr_fun
      · unfold unitCube
        exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
          isCompact_Icc |>.measurableSet
      · intro x _hx
        change ‖periodicTorusLift (complexVelocityComponent u component)
            (continuous_complexVelocityComponent hu.continuous component)
            (isOnePeriodic_complexVelocityComponent hperiodic component)
            (euclideanToSpatialTorus x)‖ ^ 2 = (u x component) ^ 2
        rw [periodicTorusLift_projection]
        simp [complexVelocityComponent, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The same complete derivative population in the Euclidean cube chart. -/
def smoothSliceDerivativeCubeSquarePopulation
    (u : InitialVelocity) (_hu : ContDiff ℝ ∞ u) (_hperiodic : IsOnePeriodic u)
    (component : Fin 3) : ℝ :=
  (∫ x in unitCube, (u x component) ^ 2) +
    (∑ i : Fin 3,
      ∫ x in unitCube, (spatialDirectionalJet u i x component) ^ 2) +
    (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x in unitCube, (secondSpatialCoordinateJet u i j x component) ^ 2) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      ∫ x in unitCube, (thirdSpatialCoordinateJet u i j l x component) ^ 2)

/-- Parseval commutes with all forty finite ordered derivative faces. -/
theorem hasSum_smoothSliceDerivativeSquarePopulation
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    HasSum (smoothSliceDerivativeSquarePopulation u hu hperiodic component)
      (smoothSliceDerivativeCubeSquarePopulation u hu hperiodic component) := by
  have hzero : HasSum (fun k ↦
      ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2)
      (∫ x in unitCube, (u x component) ^ 2) := by
    rw [← tsum_sq_smoothSliceFourierL2_eq_integral_unitCube u hu hperiodic component]
    exact (hasSum_sq_smoothSliceFourierL2 u hu hperiodic component).summable.hasSum
  have hone : HasSum (fun k ↦ ∑ i : Fin 3,
      ‖smoothSliceFourierL2 (spatialDirectionalJet u i)
        (spatialDirectionalJet_contDiff u hu i)
        (spatialDirectionalJet_isOnePeriodic u hperiodic i) component k‖ ^ 2)
      (∑ i : Fin 3,
        ∫ x in unitCube, (spatialDirectionalJet u i x component) ^ 2) := by
    apply hasSum_sum
    intro i _hi
    rw [← tsum_sq_smoothSliceFourierL2_eq_integral_unitCube
      (spatialDirectionalJet u i) (spatialDirectionalJet_contDiff u hu i)
      (spatialDirectionalJet_isOnePeriodic u hperiodic i) component]
    exact (hasSum_sq_smoothSliceFourierL2 (spatialDirectionalJet u i)
      (spatialDirectionalJet_contDiff u hu i)
      (spatialDirectionalJet_isOnePeriodic u hperiodic i) component).summable.hasSum
  have htwo : HasSum (fun k ↦ ∑ i : Fin 3, ∑ j : Fin 3,
      ‖smoothSliceFourierL2 (secondSpatialCoordinateJet u i j)
        (secondSpatialCoordinateJet_contDiff u hu i j)
        (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component k‖ ^ 2)
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in unitCube, (secondSpatialCoordinateJet u i j x component) ^ 2) := by
    apply hasSum_sum
    intro i _hi
    apply hasSum_sum
    intro j _hj
    rw [← tsum_sq_smoothSliceFourierL2_eq_integral_unitCube
      (secondSpatialCoordinateJet u i j) (secondSpatialCoordinateJet_contDiff u hu i j)
      (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component]
    exact (hasSum_sq_smoothSliceFourierL2 (secondSpatialCoordinateJet u i j)
      (secondSpatialCoordinateJet_contDiff u hu i j)
      (secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j) component).summable.hasSum
  have hthree : HasSum (fun k ↦ ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      ‖smoothSliceFourierL2 (thirdSpatialCoordinateJet u i j l)
        (thirdSpatialCoordinateJet_contDiff u hu i j l)
        (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component k‖ ^ 2)
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ∫ x in unitCube, (thirdSpatialCoordinateJet u i j l x component) ^ 2) := by
    apply hasSum_sum
    intro i _hi
    apply hasSum_sum
    intro j _hj
    apply hasSum_sum
    intro l _hl
    rw [← tsum_sq_smoothSliceFourierL2_eq_integral_unitCube
      (thirdSpatialCoordinateJet u i j l) (thirdSpatialCoordinateJet_contDiff u hu i j l)
      (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component]
    exact (hasSum_sq_smoothSliceFourierL2 (thirdSpatialCoordinateJet u i j l)
      (thirdSpatialCoordinateJet_contDiff u hu i j l)
      (thirdSpatialCoordinateJet_isOnePeriodic u hperiodic i j l) component).summable.hasSum
  have htotal := ((hzero.add hone).add htwo).add hthree
  convert htotal using 1

/-- The native scalar H³ norm is explicitly controlled by the actual complete derivative
population in the cube chart. -/
theorem norm_sq_smoothSliceWeightedH3Component_le_cubePopulation
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    ‖smoothSliceWeightedH3Component u hu hperiodic component‖ ^ 2 ≤
      3 * smoothSliceDerivativeCubeSquarePopulation u hu hperiodic component := by
  have hsource := hasPeriodicSobolevCoefficients_three_smoothSlice
    u hu hperiodic component
  have htarget :=
    (summable_smoothSliceDerivativeSquarePopulation u hu hperiodic component).mul_left 3
  have hsum := hsource.tsum_le_tsum
    (fun k ↦ periodicSobolevWeight_three_mul_norm_sq_le_population
      u hu hperiodic component k) htarget
  rw [smoothSliceWeightedH3Component,
    norm_coefficientWeightedRealization_sq_eq]
  calc
    (∑' k, periodicSobolevWeight 3 k *
        ‖(smoothSliceSobolevCoefficients u hu hperiodic component).1 k‖ ^ 2) ≤
        ∑' k, 3 * smoothSliceDerivativeSquarePopulation u hu hperiodic component k := hsum
    _ = 3 * ∑' k, smoothSliceDerivativeSquarePopulation u hu hperiodic component k :=
      tsum_mul_left
    _ = 3 * smoothSliceDerivativeCubeSquarePopulation u hu hperiodic component := by
      rw [(hasSum_smoothSliceDerivativeSquarePopulation u hu hperiodic component).tsum_eq]

/-! ## Specialization to the differentiated coordinate-energy owner -/

/-- Every component square of every addressed coordinate jet below order four is bounded, after
integration, by twice the complete coordinate H³ energy. -/
theorem openPeriodicSolutionOn_integral_coordinateJet_component_sq_le_two_energy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (n : Fin 4) (word : Fin (n : ℕ) → Fin 3) (component : Fin 3) :
    (∫ x in unitCube, (coordinateJet velocity n word x t component) ^ 2) ≤
      2 * coordinateH3Energy velocity t := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hjet := openPeriodicSolutionOn_coordinateJetSlice_contDiff
    solution ht n word
  have hleftContinuous : Continuous (fun x : Space ↦
      (coordinateJet velocity n word x t component) ^ 2) :=
    ((EuclideanSpace.proj component).continuous.comp hjet.continuous).pow 2
  have hleftInt : IntegrableOn (fun x : Space ↦
      (coordinateJet velocity n word x t component) ^ 2) unitCube :=
    hleftContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hrightInt : IntegrableOn (fun x : Space ↦
      2 * coordinateH3EnergyDensity velocity x t) unitCube :=
    (openPeriodicSolutionOn_coordinateH3EnergyDensity_integrable solution ht).const_mul 2
  have hpoint : ∀ x ∈ unitCube,
      (coordinateJet velocity n word x t component) ^ 2 ≤
        2 * coordinateH3EnergyDensity velocity x t := by
    intro x _hx
    have hcomponent :
        (coordinateJet velocity n word x t component) ^ 2 ≤
          ‖coordinateJet velocity n word x t‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun c : Fin 3 ↦ ‖coordinateJet velocity n word x t c‖ ^ 2)
        (fun c _hc ↦ sq_nonneg _)
        (Finset.mem_univ component)
      simpa [Real.norm_eq_abs, sq_abs] using hsingle
    exact hcomponent.trans
      (norm_coordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
        velocity n word x t)
  calc
    (∫ x in unitCube, (coordinateJet velocity n word x t component) ^ 2) ≤
        ∫ x in unitCube, 2 * coordinateH3EnergyDensity velocity x t :=
      setIntegral_mono_on hleftInt hrightInt hcubeMeasurable hpoint
    _ = 2 * coordinateH3Energy velocity t := by
      rw [integral_const_mul,
        ← openPeriodicSolutionOn_coordinateH3Energy_eq_integral_density solution ht]

/-- On an actual interior solution slice, the complete cube derivative population of any one
component is bounded by the forty addressed faces of the differentiated coordinate energy. -/
theorem openPeriodicSolutionOn_smoothSliceDerivativeCubeSquarePopulation_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (component : Fin 3) :
    smoothSliceDerivativeCubeSquarePopulation (fun x ↦ velocity x t)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
        (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) component ≤
      80 * coordinateH3Energy velocity t := by
  let u : InitialVelocity := fun x ↦ velocity x t
  let hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  let hp : IsOnePeriodic u := solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩
  let zeroWord : Fin 0 → Fin 3 := Fin.elim0
  have hzero :
      (∫ x in unitCube, (u x component) ^ 2) ≤
        2 * coordinateH3Energy velocity t := by
    have hbound := openPeriodicSolutionOn_integral_coordinateJet_component_sq_le_two_energy
      solution ht (⟨0, by norm_num⟩ : Fin 4) zeroWord component
    convert hbound using 1
  have hone : ∀ i : Fin 3,
      (∫ x in unitCube, (spatialDirectionalJet u i x component) ^ 2) ≤
        2 * coordinateH3Energy velocity t := by
    intro i
    have hbound := openPeriodicSolutionOn_integral_coordinateJet_component_sq_le_two_energy
      solution ht (⟨1, by norm_num⟩ : Fin 4) (firstCoordinateWord i) component
    calc
      (∫ x in unitCube, (spatialDirectionalJet u i x component) ^ 2) =
          ∫ x in unitCube, (firstCoordinateJet velocity i x t component) ^ 2 := by
        apply setIntegral_congr_fun
        · unfold unitCube
          exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
            isCompact_Icc |>.measurableSet
        · intro x _hx
          dsimp [u]
          rw [openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
            solution ht x i]
      _ ≤ 2 * coordinateH3Energy velocity t := by
        simpa [firstCoordinateJet] using hbound
  have htwo : ∀ i j : Fin 3,
      (∫ x in unitCube, (secondSpatialCoordinateJet u i j x component) ^ 2) ≤
        2 * coordinateH3Energy velocity t := by
    intro i j
    have hbound := openPeriodicSolutionOn_integral_coordinateJet_component_sq_le_two_energy
      solution ht (⟨2, by norm_num⟩ : Fin 4) (secondCoordinateWord i j) component
    calc
      (∫ x in unitCube, (secondSpatialCoordinateJet u i j x component) ^ 2) =
          ∫ x in unitCube, (secondCoordinateJet velocity i j x t component) ^ 2 := by
        apply setIntegral_congr_fun
        · unfold unitCube
          exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
            isCompact_Icc |>.measurableSet
        · intro x _hx
          dsimp [u]
          rw [openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
            solution ht x i j]
      _ ≤ 2 * coordinateH3Energy velocity t := by
        simpa [secondCoordinateJet] using hbound
  have hthree : ∀ i j l : Fin 3,
      (∫ x in unitCube, (thirdSpatialCoordinateJet u i j l x component) ^ 2) ≤
        2 * coordinateH3Energy velocity t := by
    intro i j l
    have hbound := openPeriodicSolutionOn_integral_coordinateJet_component_sq_le_two_energy
      solution ht (⟨3, by norm_num⟩ : Fin 4) (thirdCoordinateWord i j l) component
    calc
      (∫ x in unitCube, (thirdSpatialCoordinateJet u i j l x component) ^ 2) =
          ∫ x in unitCube, (thirdCoordinateJet velocity i j l x t component) ^ 2 := by
        apply setIntegral_congr_fun
        · unfold unitCube
          exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
            isCompact_Icc |>.measurableSet
        · intro x _hx
          dsimp [u]
          rw [openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
            solution ht x i j l]
      _ ≤ 2 * coordinateH3Energy velocity t := by
        simpa [thirdCoordinateJet] using hbound
  have honeSum :
      (∑ i : Fin 3, ∫ x in unitCube,
        (spatialDirectionalJet u i x component) ^ 2) ≤
        ∑ _i : Fin 3, 2 * coordinateH3Energy velocity t :=
    Finset.sum_le_sum (fun i _hi ↦ hone i)
  have htwoSum :
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ x in unitCube,
        (secondSpatialCoordinateJet u i j x component) ^ 2) ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3, 2 * coordinateH3Energy velocity t :=
    Finset.sum_le_sum (fun i _hi ↦ Finset.sum_le_sum (fun j _hj ↦ htwo i j))
  have hthreeSum :
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∫ x in unitCube,
        (thirdSpatialCoordinateJet u i j l x component) ^ 2) ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3,
          2 * coordinateH3Energy velocity t :=
    Finset.sum_le_sum (fun i _hi ↦ Finset.sum_le_sum (fun j _hj ↦
      Finset.sum_le_sum (fun l _hl ↦ hthree i j l)))
  change smoothSliceDerivativeCubeSquarePopulation u hu hp component ≤ _
  unfold smoothSliceDerivativeCubeSquarePopulation
  calc
    (∫ x in unitCube, (u x component) ^ 2) +
        (∑ i : Fin 3, ∫ x in unitCube,
          (spatialDirectionalJet u i x component) ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x in unitCube,
          (secondSpatialCoordinateJet u i j x component) ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∫ x in unitCube,
          (thirdSpatialCoordinateJet u i j l x component) ^ 2) ≤
      2 * coordinateH3Energy velocity t +
        (∑ _i : Fin 3, 2 * coordinateH3Energy velocity t) +
        (∑ _i : Fin 3, ∑ _j : Fin 3, 2 * coordinateH3Energy velocity t) +
        (∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3,
          2 * coordinateH3Energy velocity t) :=
      add_le_add (add_le_add (add_le_add hzero honeSum) htwoSum) hthreeSum
    _ = 80 * coordinateH3Energy velocity t := by norm_num; ring

/-- Every actual interior component enters native weighted H³ with a squared norm controlled by
the differentiated coordinate energy. -/
theorem openPeriodicSolutionOn_norm_sq_smoothSliceWeightedH3Component_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (component : Fin 3) :
    ‖smoothSliceWeightedH3Component (fun x ↦ velocity x t)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
        (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) component‖ ^ 2 ≤
      240 * coordinateH3Energy velocity t := by
  have hnative := norm_sq_smoothSliceWeightedH3Component_le_cubePopulation
    (fun x ↦ velocity x t) (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
    (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) component
  have hcube := openPeriodicSolutionOn_smoothSliceDerivativeCubeSquarePopulation_le
    solution ht component
  calc
    _ ≤ 3 * smoothSliceDerivativeCubeSquarePopulation (fun x ↦ velocity x t)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
        (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) component := hnative
    _ ≤ 3 * (80 * coordinateH3Energy velocity t) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    _ = 240 * coordinateH3Energy velocity t := by ring

/-- **Actual vector-slice H³ bridge.**  All three components of every admitted interior
solution slice form one complete native weighted H³ population, with an explicit squared norm
bound.  The product norm is the componentwise supremum, so no extra factor of three is lost. -/
theorem openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
        (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)‖ ^ 2 ≤
      240 * coordinateH3Energy velocity t := by
  let state : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 (fun x ↦ velocity x t)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)
  let C : ℝ := 240 * coordinateH3Energy velocity t
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (coordinateH3Energy_nonneg velocity t)
  have hcomponentSq : ∀ component : Fin 3, ‖state component‖ ^ 2 ≤ C := by
    intro component
    exact openPeriodicSolutionOn_norm_sq_smoothSliceWeightedH3Component_le
      solution ht component
  have hcomponent : ∀ component : Fin 3, ‖state component‖ ≤ Real.sqrt C := by
    intro component
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
    rw [Real.sq_sqrt hC]
    exact hcomponentSq component
  have hstate : ‖state‖ ≤ Real.sqrt C :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg C)).2 hcomponent
  change ‖state‖ ^ 2 ≤ C
  calc
    ‖state‖ ^ 2 ≤ (Real.sqrt C) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mpr hstate
    _ = C := Real.sq_sqrt hC

/-- The same vector bridge against the positive logarithmic receiver used by the continuation
line. -/
theorem openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le_logReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
        (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)‖ ^ 2 ≤
      240 * coordinateLogH3Receiver velocity t := by
  have henergy := openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le solution ht
  calc
    _ ≤ 240 * coordinateH3Energy velocity t := henergy
    _ ≤ 240 * coordinateLogH3Receiver velocity t := by
      unfold coordinateLogH3Receiver
      have hexp : 0 ≤ Real.exp 1 := Real.exp_pos 1 |>.le
      nlinarith

section Audit

#print axioms smoothSliceFourierL2
#print axioms hasSum_sq_smoothSliceFourierL2
#print axioms smoothSliceFourierL2_spatialDirectionalJet
#print axioms hasPeriodicSobolevCoefficients_three_smoothSlice
#print axioms smoothSliceVectorWeightedH3
#print axioms unweighted_smoothSliceVectorWeightedH3_apply
#print axioms norm_sq_smoothSliceWeightedH3Component_le_cubePopulation
#print axioms openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le
#print axioms openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le_logReceiver

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
