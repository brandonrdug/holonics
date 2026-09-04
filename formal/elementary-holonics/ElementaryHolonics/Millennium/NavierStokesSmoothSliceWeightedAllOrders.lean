import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3
import ElementaryHolonics.Millennium.NavierStokesWeightedOrderRestriction

/-!
# Every smooth periodic slice enters every finite native Sobolev scale

**[proved-derived]** The order-three restart bridge already uses actual torus Fourier
coefficients and Parseval for the `1 + 3 + 9 + 27` coordinate population.  A smooth periodic
slice carries the same construction at every finite order.  This owner retains an arbitrary
ordered coordinate word, proves its exact multiplier product, sums the complete word population
to the corresponding Stokes power, and returns the original coefficient population in native
weighted order `m`.

No uniform-in-`m` estimate or analytic/Gevrey conclusion is asserted.  Each finite order is one
separately addressed receiver of the same smooth source occurrence.
-/

noncomputable section

open ContDiff MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Arbitrary ordered coordinate jets -/

/-- Apply an addressed word of spatial coordinate derivatives.  The head coordinate is the
outermost derivative and the tail retains the earlier passage. -/
def spatialCoordinateWordJet (u : InitialVelocity) :
    (order : ℕ) → (Fin order → Fin 3) → InitialVelocity
  | 0, _word => u
  | order + 1, word =>
      spatialDirectionalJet
        (spatialCoordinateWordJet u order (Fin.tail word)) (word 0)

/-- Smoothness survives every finite ordered coordinate word. -/
theorem spatialCoordinateWordJet_contDiff
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) :
    ∀ (order : ℕ) (word : Fin order → Fin 3),
      ContDiff ℝ ∞ (spatialCoordinateWordJet u order word)
  | 0, _word => hu
  | order + 1, word =>
      spatialDirectionalJet_contDiff _
        (spatialCoordinateWordJet_contDiff u hu order (Fin.tail word)) (word 0)

/-- Periodicity survives every finite ordered coordinate word. -/
theorem spatialCoordinateWordJet_isOnePeriodic
    (u : InitialVelocity) (hperiodic : IsOnePeriodic u) :
    ∀ (order : ℕ) (word : Fin order → Fin 3),
      IsOnePeriodic (spatialCoordinateWordJet u order word)
  | 0, _word => hperiodic
  | order + 1, word =>
      spatialDirectionalJet_isOnePeriodic _
        (spatialCoordinateWordJet_isOnePeriodic u hperiodic order (Fin.tail word)) (word 0)

/-- The exact unit-torus derivative multiplier at one coordinate pin. -/
def coordinateFourierMultiplier
    (coordinate : Fin 3) (k : SpatialFrequency) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)

/-- The Fourier coefficient of an arbitrary coordinate word is the product of its addressed
unit-torus multipliers times the source coefficient. -/
theorem smoothSliceFourierL2_spatialCoordinateWordJet
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    ∀ (order : ℕ) (word : Fin order → Fin 3) (k : SpatialFrequency),
      smoothSliceFourierL2 (spatialCoordinateWordJet u order word)
          (spatialCoordinateWordJet_contDiff u hu order word)
          (spatialCoordinateWordJet_isOnePeriodic u hperiodic order word) component k =
        (∏ index : Fin order, coordinateFourierMultiplier (word index) k) *
          smoothSliceFourierL2 u hu hperiodic component k
  | 0, _word, _k => by simp [spatialCoordinateWordJet]
  | order + 1, word, k => by
      let tailJet := spatialCoordinateWordJet u order (Fin.tail word)
      let htailSmooth := spatialCoordinateWordJet_contDiff u hu order (Fin.tail word)
      let htailPeriodic :=
        spatialCoordinateWordJet_isOnePeriodic u hperiodic order (Fin.tail word)
      calc
        smoothSliceFourierL2
            (spatialDirectionalJet tailJet (word 0))
            (spatialDirectionalJet_contDiff tailJet htailSmooth (word 0))
            (spatialDirectionalJet_isOnePeriodic tailJet htailPeriodic (word 0))
            component k =
          coordinateFourierMultiplier (word 0) k *
            smoothSliceFourierL2 tailJet htailSmooth htailPeriodic component k := by
              simpa [coordinateFourierMultiplier] using
                smoothSliceFourierL2_spatialDirectionalJet
                  tailJet htailSmooth htailPeriodic (word 0) component k
        _ = coordinateFourierMultiplier (word 0) k *
            ((∏ index : Fin order,
                coordinateFourierMultiplier ((Fin.tail word) index) k) *
              smoothSliceFourierL2 u hu hperiodic component k) := by
              rw [smoothSliceFourierL2_spatialCoordinateWordJet
                u hu hperiodic component order (Fin.tail word) k]
        _ = (∏ index : Fin (order + 1),
              coordinateFourierMultiplier (word index) k) *
            smoothSliceFourierL2 u hu hperiodic component k := by
              rw [Fin.prod_univ_succ]
              simp only [Fin.tail]
              ac_rfl

/-! ## The complete top-order population -/

theorem norm_coordinateFourierMultiplier_sq
    (coordinate : Fin 3) (k : SpatialFrequency) :
    ‖coordinateFourierMultiplier coordinate k‖ ^ 2 =
      coordinateStokesEigenvalue coordinate k := by
  simp [coordinateFourierMultiplier, coordinateStokesEigenvalue,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  rw [mul_pow, sq_abs]

/-- Squaring the coefficient of one word exposes the product of its coordinate Stokes faces. -/
theorem norm_sq_smoothSliceFourierL2_spatialCoordinateWordJet
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (order : ℕ) (word : Fin order → Fin 3)
    (k : SpatialFrequency) :
    ‖smoothSliceFourierL2 (spatialCoordinateWordJet u order word)
        (spatialCoordinateWordJet_contDiff u hu order word)
        (spatialCoordinateWordJet_isOnePeriodic u hperiodic order word) component k‖ ^ 2 =
      (∏ index : Fin order, coordinateStokesEigenvalue (word index) k) *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  rw [smoothSliceFourierL2_spatialCoordinateWordJet
    u hu hperiodic component order word k, norm_mul, mul_pow]
  congr 1
  rw [norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro index _hindex
  exact norm_coordinateFourierMultiplier_sq (word index) k

/-- Summing every addressed word of length `order` is exactly the corresponding Stokes power. -/
theorem sum_norm_sq_smoothSliceFourierL2_spatialCoordinateWordJet
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (order : ℕ) (k : SpatialFrequency) :
    (∑ word : Fin order → Fin 3,
      ‖smoothSliceFourierL2 (spatialCoordinateWordJet u order word)
          (spatialCoordinateWordJet_contDiff u hu order word)
          (spatialCoordinateWordJet_isOnePeriodic u hperiodic order word)
          component k‖ ^ 2) =
      (torusStokesEigenvalue k) ^ order *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  apply Eq.trans (Finset.sum_congr rfl (fun word _hword ↦
    norm_sq_smoothSliceFourierL2_spatialCoordinateWordJet
      u hu hperiodic component order word k))
  rw [← Finset.sum_mul]
  rw [← Fintype.sum_pow
    (fun coordinate : Fin 3 ↦ coordinateStokesEigenvalue coordinate k) order]
  rw [← torusStokesEigenvalue_eq_sum_coordinate]

/-- The complete top-word square population is summable over the full integer lattice. -/
theorem summable_stokesPower_mul_norm_sq_smoothSliceFourierL2
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (order : ℕ) :
    Summable fun k : SpatialFrequency ↦
      (torusStokesEigenvalue k) ^ order *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
  have hwords : Summable fun k : SpatialFrequency ↦
      ∑ word : Fin order → Fin 3,
        ‖smoothSliceFourierL2 (spatialCoordinateWordJet u order word)
          (spatialCoordinateWordJet_contDiff u hu order word)
          (spatialCoordinateWordJet_isOnePeriodic u hperiodic order word)
          component k‖ ^ 2 := by
    apply summable_sum
    intro word _hword
    exact (hasSum_sq_smoothSliceFourierL2
      (spatialCoordinateWordJet u order word)
      (spatialCoordinateWordJet_contDiff u hu order word)
      (spatialCoordinateWordJet_isOnePeriodic u hperiodic order word)
      component).summable
  exact hwords.congr (fun k ↦
    sum_norm_sq_smoothSliceFourierL2_spatialCoordinateWordJet
      u hu hperiodic component order k)

/-! ## Entry into arbitrary finite weighted order -/

theorem periodicSobolevWeight_le_twoPow_mul_one_add_stokesPower
    (order : ℕ) (k : SpatialFrequency) :
    periodicSobolevWeight order k ≤
      (2 : ℝ) ^ order * (1 + (torusStokesEigenvalue k) ^ order) := by
  let x := torusStokesEigenvalue k
  have hx : 0 ≤ x := torusStokesEigenvalue_nonneg k
  unfold periodicSobolevWeight
  change (1 + x) ^ order ≤ (2 : ℝ) ^ order * (1 + x ^ order)
  rcases le_total x 1 with hxone | honex
  · have hbase : 1 + x ≤ 2 := by linarith
    have hpow := pow_le_pow_left₀ (add_nonneg zero_le_one hx) hbase order
    have hone : 1 ≤ 1 + x ^ order :=
      le_add_of_nonneg_right (pow_nonneg hx order)
    exact hpow.trans (le_mul_of_one_le_right (pow_nonneg (by norm_num) _) hone)
  · have hbase : 1 + x ≤ 2 * x := by linarith
    have hpow := pow_le_pow_left₀ (add_nonneg zero_le_one hx) hbase order
    calc
      (1 + x) ^ order ≤ (2 * x) ^ order := hpow
      _ = 2 ^ order * x ^ order := by rw [mul_pow]
      _ ≤ 2 ^ order * (1 + x ^ order) := by
        gcongr
        linarith

/-- The actual Fourier coefficient population of a smooth periodic component has every finite
Sobolev order. -/
theorem hasPeriodicSobolevCoefficients_smoothSlice
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (order : ℕ) :
    HasPeriodicSobolevCoefficients order
      (smoothSliceFourierL2 u hu hperiodic component) := by
  have hzero : Summable fun k : SpatialFrequency ↦
      ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
    exact (hasSum_sq_smoothSliceFourierL2 u hu hperiodic component).summable
  have htop := summable_stokesPower_mul_norm_sq_smoothSliceFourierL2
    u hu hperiodic component order
  have hsource : Summable fun k : SpatialFrequency ↦
      (2 : ℝ) ^ order *
        (‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 +
          (torusStokesEigenvalue k) ^ order *
            ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2) :=
    (hzero.add htop).mul_left ((2 : ℝ) ^ order)
  unfold HasPeriodicSobolevCoefficients
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg order k) (sq_nonneg _))
    (fun k ↦ ?_) hsource
  have hweight := periodicSobolevWeight_le_twoPow_mul_one_add_stokesPower order k
  calc
    periodicSobolevWeight order k *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 ≤
      ((2 : ℝ) ^ order * (1 + (torusStokesEigenvalue k) ^ order)) *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ = (2 : ℝ) ^ order *
        (‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 +
          (torusStokesEigenvalue k) ^ order *
            ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2) := by ring

/-- One actual smooth component in the native complete carrier of arbitrary finite order. -/
def smoothSliceWeightedComponent
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (order : ℕ) (component : Fin 3) : PeriodicWeightedSobolev order :=
  coefficientWeightedRealization order
    ⟨smoothSliceFourierL2 u hu hperiodic component,
      hasPeriodicSobolevCoefficients_smoothSlice
        u hu hperiodic component order⟩

/-- The complete three-component smooth slice at arbitrary finite native order. -/
def smoothSliceVectorWeighted
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (order : ℕ) : PeriodicVectorWeightedSobolev order :=
  fun component ↦ smoothSliceWeightedComponent u hu hperiodic order component

/-- Unweighting any finite native order returns the same actual source Fourier coefficient. -/
theorem unweighted_smoothSliceVectorWeighted_apply
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients order
      (smoothSliceVectorWeighted u hu hperiodic order component)).1 k =
        vectorSpatialFourierCoeff u hu.continuous hperiodic k component := by
  unfold smoothSliceVectorWeighted smoothSliceWeightedComponent
  have hreconstruct := weightedSobolevCoefficients_coefficientWeightedRealization order
    (⟨smoothSliceFourierL2 u hu hperiodic component,
      hasPeriodicSobolevCoefficients_smoothSlice
        u hu hperiodic component order⟩ : PeriodicSobolevCoefficients order)
  have hcoefficient := congrArg
    (fun coeff : PeriodicSobolevCoefficients order ↦ coeff.1 k) hreconstruct
  exact hcoefficient.trans (smoothSliceFourierL2_apply u hu hperiodic component k)

section Audit

#print axioms spatialCoordinateWordJet_contDiff
#print axioms smoothSliceFourierL2_spatialCoordinateWordJet
#print axioms sum_norm_sq_smoothSliceFourierL2_spatialCoordinateWordJet
#print axioms hasPeriodicSobolevCoefficients_smoothSlice
#print axioms smoothSliceVectorWeighted
#print axioms unweighted_smoothSliceVectorWeighted_apply

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders
