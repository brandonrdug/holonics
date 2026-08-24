import ElementaryHolonics.Millennium.NavierStokesWeightedOrderRestriction
import ElementaryHolonics.Millennium.NavierStokesWeightedLerayBilinear

/-!
# Higher-order tame Fourier multiplication on the native Sobolev scale

For every natural order `m ≥ 3`, this owner retains the complete integer Fourier population and
constructs the scalar product at order `m`.  Its estimate is tame: the high-order norm can land on
either factor, while the other factor is observed only through the exact high-to-`H³` restriction.
The same population is then available for spending one derivative and applying the modewise Leray
face.

All constants are explicit and deliberately coarse.  No frequency aperture is introduced.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Scale-uniform Sobolev amplitude interaction -/

/-- The positive square root of the exact order-`m` inhomogeneous Fourier weight. -/
def sobolevAmplitudeAtOrder (order : ℕ) (k : SpatialFrequency) : ℝ :=
  Real.sqrt (periodicSobolevWeight order k)

theorem sobolevAmplitudeAtOrder_nonneg (order : ℕ) (k : SpatialFrequency) :
    0 ≤ sobolevAmplitudeAtOrder order k :=
  Real.sqrt_nonneg _

theorem sobolevAmplitudeAtOrder_sq (order : ℕ) (k : SpatialFrequency) :
    sobolevAmplitudeAtOrder order k ^ 2 = periodicSobolevWeight order k := by
  rw [sobolevAmplitudeAtOrder,
    Real.sq_sqrt (periodicSobolevWeight_nonneg order k)]

/-- A coarse natural-power convexity bound that keeps the exponent symbolic. -/
theorem add_pow_le_two_pow_mul_add_pow
    (order : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ order ≤
      (2 : ℝ) ^ order * (a ^ order + b ^ order) := by
  by_cases hab : a ≤ b
  · have hab' : a + b ≤ 2 * b := by linarith
    calc
      (a + b) ^ order ≤ (2 * b) ^ order :=
        pow_le_pow_left₀ (add_nonneg ha hb) hab' order
      _ = (2 : ℝ) ^ order * b ^ order := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ order * (a ^ order + b ^ order) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (pow_nonneg ha order))
          (pow_nonneg (by norm_num) order)
  · have hba : b ≤ a := le_of_not_ge hab
    have hba' : a + b ≤ 2 * a := by linarith
    calc
      (a + b) ^ order ≤ (2 * a) ^ order :=
        pow_le_pow_left₀ (add_nonneg ha hb) hba' order
      _ = (2 : ℝ) ^ order * a ^ order := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ order * (a ^ order + b ^ order) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (pow_nonneg hb order))
          (pow_nonneg (by norm_num) order)

/-- The exact order-`m` weight at a summed mode is controlled by the two input weights. -/
theorem periodicSobolevWeight_add_le
    (order : ℕ) (p q : SpatialFrequency) :
    periodicSobolevWeight order (p + q) ≤
      ((2 : ℝ) ^ order) ^ 2 *
        (periodicSobolevWeight order p + periodicSobolevWeight order q) := by
  let a := periodicSobolevWeight 1 p
  let b := periodicSobolevWeight 1 q
  let c := periodicSobolevWeight 1 (p + q)
  have ha : 0 ≤ a := periodicSobolevWeight_nonneg 1 p
  have hb : 0 ≤ b := periodicSobolevWeight_nonneg 1 q
  have hc : 0 ≤ c := periodicSobolevWeight_nonneg 1 (p + q)
  have hc_le : c ≤ 2 * (a + b) := periodicSobolevWeight_one_add_le p q
  have hpower := pow_le_pow_left₀ hc hc_le order
  have hadd := add_pow_le_two_pow_mul_add_pow order ha hb
  calc
    periodicSobolevWeight order (p + q) = c ^ order := by
      simp [c, periodicSobolevWeight]
    _ ≤ (2 * (a + b)) ^ order := hpower
    _ = (2 : ℝ) ^ order * (a + b) ^ order := by rw [mul_pow]
    _ ≤ (2 : ℝ) ^ order *
        ((2 : ℝ) ^ order * (a ^ order + b ^ order)) :=
      mul_le_mul_of_nonneg_left hadd (pow_nonneg (by norm_num) order)
    _ = ((2 : ℝ) ^ order) ^ 2 *
        (periodicSobolevWeight order p + periodicSobolevWeight order q) := by
      simp [a, b, periodicSobolevWeight]
      ring

/-- Generic amplitude subadditivity.  At order `m` the retained constant is exactly `2^m`. -/
theorem sobolevAmplitudeAtOrder_add_le
    (order : ℕ) (p q : SpatialFrequency) :
    sobolevAmplitudeAtOrder order (p + q) ≤
      (2 : ℝ) ^ order *
        (sobolevAmplitudeAtOrder order p + sobolevAmplitudeAtOrder order q) := by
  have hweight := periodicSobolevWeight_add_le order p q
  rw [← sobolevAmplitudeAtOrder_sq order (p + q),
    ← sobolevAmplitudeAtOrder_sq order p,
    ← sobolevAmplitudeAtOrder_sq order q] at hweight
  let C := (2 : ℝ) ^ order
  let A := sobolevAmplitudeAtOrder order p
  let B := sobolevAmplitudeAtOrder order q
  let D := sobolevAmplitudeAtOrder order (p + q)
  have hC : 0 ≤ C := pow_nonneg (by norm_num) order
  have hA : 0 ≤ A := sobolevAmplitudeAtOrder_nonneg order p
  have hB : 0 ≤ B := sobolevAmplitudeAtOrder_nonneg order q
  have hD : 0 ≤ D := sobolevAmplitudeAtOrder_nonneg order (p + q)
  have hab : A ^ 2 + B ^ 2 ≤ (A + B) ^ 2 := by
    nlinarith [mul_nonneg hA hB]
  have hscaled : C ^ 2 * (A ^ 2 + B ^ 2) ≤ C ^ 2 * (A + B) ^ 2 :=
    mul_le_mul_of_nonneg_left hab (sq_nonneg C)
  change D ≤ C * (A + B)
  change D ^ 2 ≤ C ^ 2 * (A ^ 2 + B ^ 2) at hweight
  have hsquare : D ^ 2 ≤ (C * (A + B)) ^ 2 := by
    calc
      D ^ 2 ≤ C ^ 2 * (A ^ 2 + B ^ 2) := hweight
      _ ≤ C ^ 2 * (A + B) ^ 2 := hscaled
      _ = (C * (A + B)) ^ 2 := by ring
  nlinarith [mul_nonneg hC (add_nonneg hA hB),
    sq_nonneg (D + C * (A + B))]

/-! ## Exact order-`m` coefficient norm and the retained `H³` receiver -/

/-- The complete nonnegative order-`m` weighted coefficient population. -/
def weightedAbsoluteCoefficientAtOrder
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) :
    PeriodicRealFourierL2 :=
  ⟨fun k ↦ sobolevAmplitudeAtOrder order k * ‖coeff.1 k‖, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hnonneg (k : SpatialFrequency) :
        0 ≤ sobolevAmplitudeAtOrder order k * ‖coeff.1 k‖ :=
      mul_nonneg (sobolevAmplitudeAtOrder_nonneg order k) (norm_nonneg _)
    simpa only [Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg _), mul_pow,
      sobolevAmplitudeAtOrder_sq] using coeff.2⟩

/-- The exact scalar order-`m` coefficient norm. -/
def periodicSobolevCoefficientNorm
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) : ℝ :=
  ‖weightedAbsoluteCoefficientAtOrder order coeff‖

theorem periodicSobolevCoefficientNorm_nonneg
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) :
    0 ≤ periodicSobolevCoefficientNorm order coeff :=
  norm_nonneg _

/-- Exact agreement between the real amplitude receiver and the native complex Hilbert norm. -/
theorem periodicSobolevCoefficientNorm_eq_nativeNorm
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) :
    periodicSobolevCoefficientNorm order coeff =
      ‖coefficientWeightedRealization order coeff‖ := by
  have hleft := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (weightedAbsoluteCoefficientAtOrder order coeff)
  have hleftSquare : periodicSobolevCoefficientNorm order coeff ^ 2 =
      ∑' k, periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2 := by
    rw [periodicSobolevCoefficientNorm]
    calc
      ‖weightedAbsoluteCoefficientAtOrder order coeff‖ ^ 2 =
          ∑' k, ‖weightedAbsoluteCoefficientAtOrder order coeff k‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hleft
      _ = ∑' k, periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2 := by
        apply tsum_congr
        intro k
        simp only [weightedAbsoluteCoefficientAtOrder, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg
            (sobolevAmplitudeAtOrder_nonneg order k) (norm_nonneg _)),
          mul_pow, sobolevAmplitudeAtOrder_sq]
  have hrightSquare := norm_coefficientWeightedRealization_sq_eq order coeff
  nlinarith [periodicSobolevCoefficientNorm_nonneg order coeff,
    norm_nonneg (coefficientWeightedRealization order coeff)]

/-- Unweighting a native order-`m` state preserves its exact norm. -/
theorem periodicSobolevCoefficientNorm_weightedSobolevCoefficients
    (order : ℕ) (state : PeriodicWeightedSobolev order) :
    periodicSobolevCoefficientNorm order
        (weightedSobolevCoefficients order state) = ‖state‖ := by
  rw [periodicSobolevCoefficientNorm_eq_nativeNorm,
    coefficientWeightedRealization_weightedSobolevCoefficients]

/-- The order-three receiver of a higher coefficient population. -/
def restrictCoefficientsToThree
    (order : ℕ) (horder : 3 ≤ order)
    (coeff : PeriodicSobolevCoefficients order) :
    PeriodicSobolevCoefficients 3 :=
  periodicSobolevCoefficientsRestrict 3 order horder coeff

@[simp]
theorem restrictCoefficientsToThree_apply
    (order : ℕ) (horder : 3 ≤ order)
    (coeff : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    (restrictCoefficientsToThree order horder coeff).1 k = coeff.1 k :=
  rfl

/-- Every order at least three retains an absolutely summable raw coefficient population. -/
theorem summable_norm_periodicSobolevCoefficient_of_three_le
    (order : ℕ) (horder : 3 ≤ order)
    (coeff : PeriodicSobolevCoefficients order) :
    Summable fun k ↦ ‖coeff.1 k‖ := by
  simpa only [restrictCoefficientsToThree_apply] using
    summable_norm_periodicSobolevThreeCoefficient
      (restrictCoefficientsToThree order horder coeff)

/-! ## Complete scalar multiplication at every order `m ≥ 3` -/

/-- The complete complex convolution, constructed through the retained order-three `ℓ¹`
receiver but keeping exactly the source order-`m` coefficients. -/
def scalarSobolevProductConvolution
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) : PeriodicFourierL2 :=
  scalarH3ProductConvolution
    (restrictCoefficientsToThree order horder left)
    (restrictCoefficientsToThree order horder right)

/-- Exact coefficient law of the complete higher-order product population. -/
theorem scalarSobolevProductConvolution_apply
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    scalarSobolevProductConvolution order horder left right k =
      ∑' p, left.1 p * right.1 (k - p) := by
  simpa only [scalarSobolevProductConvolution,
    restrictCoefficientsToThree_apply] using
      scalarH3ProductConvolution_apply
        (restrictCoefficientsToThree order horder left)
        (restrictCoefficientsToThree order horder right) k

/-- The positive Young envelope with the order-`m` amplitude placed on either factor. -/
def scalarSobolevProductEnvelope
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) : PeriodicRealFourierL2 :=
  ((2 : ℝ) ^ order) •
    (realL1L2FourierConvolution
        (absoluteCoefficient (restrictCoefficientsToThree order horder left))
        (weightedAbsoluteCoefficientAtOrder order right) +
      realL1L2FourierConvolution
        (absoluteCoefficient (restrictCoefficientsToThree order horder right))
        (weightedAbsoluteCoefficientAtOrder order left))

/-- Every coefficient of the generic product envelope is nonnegative. -/
theorem scalarSobolevProductEnvelope_nonneg
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    0 ≤ scalarSobolevProductEnvelope order horder left right k := by
  let leftThree := restrictCoefficientsToThree order horder left
  let rightThree := restrictCoefficientsToThree order horder right
  change 0 ≤ (2 : ℝ) ^ order *
    (realL1L2FourierConvolution (absoluteCoefficient leftThree)
        (weightedAbsoluteCoefficientAtOrder order right) k +
      realL1L2FourierConvolution (absoluteCoefficient rightThree)
        (weightedAbsoluteCoefficientAtOrder order left) k)
  rw [realL1L2FourierConvolution_apply
      (summable_norm_absoluteCoefficient leftThree),
    realL1L2FourierConvolution_apply
      (summable_norm_absoluteCoefficient rightThree)]
  refine mul_nonneg (pow_nonneg (by norm_num) order)
    (add_nonneg (tsum_nonneg fun p ↦ ?_) (tsum_nonneg fun p ↦ ?_))
  · exact mul_nonneg (norm_nonneg _)
      (mul_nonneg (sobolevAmplitudeAtOrder_nonneg order _) (norm_nonneg _))
  · exact mul_nonneg (norm_nonneg _)
      (mul_nonneg (sobolevAmplitudeAtOrder_nonneg order _) (norm_nonneg _))

private theorem summable_scalarSobolevProduct_norm_terms
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    Summable fun p ↦ ‖left.1 p * right.1 (k - p)‖ := by
  have hleft := summable_norm_periodicSobolevCoefficient_of_three_le
    order horder left
  have hbound : Summable fun p ↦ ‖left.1 p‖ * ‖right.1‖ :=
    hleft.mul_right ‖right.1‖
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) right.1 (k - p))
    (norm_nonneg _)

private theorem summable_first_orderWeighted_product_terms
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    Summable fun p ↦
      ‖left.1 p‖ *
        (sobolevAmplitudeAtOrder order (k - p) * ‖right.1 (k - p)‖) := by
  have hleft := summable_norm_periodicSobolevCoefficient_of_three_le
    order horder left
  have hbound : Summable fun p ↦
      ‖left.1 p‖ * ‖weightedAbsoluteCoefficientAtOrder order right‖ :=
    hleft.mul_right ‖weightedAbsoluteCoefficientAtOrder order right‖
  refine Summable.of_nonneg_of_le
    (fun p ↦ mul_nonneg (norm_nonneg _)
      (mul_nonneg (sobolevAmplitudeAtOrder_nonneg order _) (norm_nonneg _)))
    (fun p ↦ ?_) hbound
  have heval := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (weightedAbsoluteCoefficientAtOrder order right) (k - p)
  have hweightedNonneg :
      0 ≤ sobolevAmplitudeAtOrder order (k - p) * ‖right.1 (k - p)‖ :=
    mul_nonneg (sobolevAmplitudeAtOrder_nonneg order _) (norm_nonneg _)
  have heval' :
      sobolevAmplitudeAtOrder order (k - p) * ‖right.1 (k - p)‖ ≤
        ‖weightedAbsoluteCoefficientAtOrder order right‖ := by
    simpa only [weightedAbsoluteCoefficientAtOrder, Real.norm_eq_abs,
      abs_of_nonneg hweightedNonneg] using heval
  exact mul_le_mul_of_nonneg_left heval' (norm_nonneg _)

private theorem summable_second_orderWeighted_product_terms
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    Summable fun p ↦
      (sobolevAmplitudeAtOrder order p * ‖left.1 p‖) *
        ‖right.1 (k - p)‖ := by
  let reflected : SpatialFrequency ≃ SpatialFrequency := Equiv.subLeft k
  have hright := summable_norm_periodicSobolevCoefficient_of_three_le
    order horder right
  have hbase : Summable fun q ↦
      ‖right.1 q‖ * ‖weightedAbsoluteCoefficientAtOrder order left‖ :=
    hright.mul_right ‖weightedAbsoluteCoefficientAtOrder order left‖
  have hshiftedBase : Summable fun q ↦
      ‖right.1 q‖ *
        (sobolevAmplitudeAtOrder order (k - q) * ‖left.1 (k - q)‖) := by
    refine Summable.of_nonneg_of_le
      (fun q ↦ mul_nonneg (norm_nonneg _)
        (mul_nonneg (sobolevAmplitudeAtOrder_nonneg order _) (norm_nonneg _)))
      (fun q ↦ ?_) hbase
    have heval := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (weightedAbsoluteCoefficientAtOrder order left) (k - q)
    have hweightedNonneg :
        0 ≤ sobolevAmplitudeAtOrder order (k - q) * ‖left.1 (k - q)‖ :=
      mul_nonneg (sobolevAmplitudeAtOrder_nonneg order _) (norm_nonneg _)
    have heval' :
        sobolevAmplitudeAtOrder order (k - q) * ‖left.1 (k - q)‖ ≤
          ‖weightedAbsoluteCoefficientAtOrder order left‖ := by
      simpa only [weightedAbsoluteCoefficientAtOrder, Real.norm_eq_abs,
        abs_of_nonneg hweightedNonneg] using heval
    exact mul_le_mul_of_nonneg_left heval' (norm_nonneg _)
  have hreindexed := reflected.summable_iff.mpr hshiftedBase
  refine hreindexed.congr ?_
  intro p
  simp only [Function.comp_apply, reflected, Equiv.subLeft_apply]
  ring_nf

/-- The weighted complete product coefficient is controlled pointwise by its tame Young
envelope. -/
theorem norm_sobolevAmplitudeAtOrder_mul_scalarSobolevProductConvolution_le_envelope
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    ‖(sobolevAmplitudeAtOrder order k : ℂ) *
        scalarSobolevProductConvolution order horder left right k‖ ≤
      scalarSobolevProductEnvelope order horder left right k := by
  have hplain := summable_scalarSobolevProduct_norm_terms order horder left right k
  have hfirst := summable_first_orderWeighted_product_terms
    order horder left right k
  have hsecond := summable_second_orderWeighted_product_terms
    order horder left right k
  have hright : Summable fun p ↦ (2 : ℝ) ^ order *
      (‖left.1 p‖ *
          (sobolevAmplitudeAtOrder order (k - p) * ‖right.1 (k - p)‖) +
        (sobolevAmplitudeAtOrder order p * ‖left.1 p‖) *
          ‖right.1 (k - p)‖) :=
    (hfirst.add hsecond).mul_left ((2 : ℝ) ^ order)
  have hweightedPlain : Summable fun p ↦
      sobolevAmplitudeAtOrder order k * ‖left.1 p * right.1 (k - p)‖ :=
    hplain.mul_left (sobolevAmplitudeAtOrder order k)
  have hterm : ∀ p,
      sobolevAmplitudeAtOrder order k * ‖left.1 p * right.1 (k - p)‖ ≤
        (2 : ℝ) ^ order *
          (‖left.1 p‖ *
              (sobolevAmplitudeAtOrder order (k - p) * ‖right.1 (k - p)‖) +
            (sobolevAmplitudeAtOrder order p * ‖left.1 p‖) *
              ‖right.1 (k - p)‖) := by
    intro p
    have hsum : p + (k - p) = k := by abel
    have hweight := sobolevAmplitudeAtOrder_add_le order p (k - p)
    rw [hsum] at hweight
    rw [norm_mul]
    have hmul := mul_le_mul_of_nonneg_right hweight
      (mul_nonneg (norm_nonneg (left.1 p)) (norm_nonneg (right.1 (k - p))))
    nlinarith
  calc
    ‖(sobolevAmplitudeAtOrder order k : ℂ) *
        scalarSobolevProductConvolution order horder left right k‖ =
        sobolevAmplitudeAtOrder order k *
          ‖scalarSobolevProductConvolution order horder left right k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sobolevAmplitudeAtOrder_nonneg order k)]
    _ ≤ sobolevAmplitudeAtOrder order k *
        (∑' p, ‖left.1 p * right.1 (k - p)‖) := by
      apply mul_le_mul_of_nonneg_left _ (sobolevAmplitudeAtOrder_nonneg order k)
      rw [scalarSobolevProductConvolution_apply]
      exact norm_tsum_le_tsum_norm hplain
    _ = ∑' p, sobolevAmplitudeAtOrder order k *
        ‖left.1 p * right.1 (k - p)‖ := by
      rw [hplain.tsum_mul_left]
    _ ≤ ∑' p, (2 : ℝ) ^ order *
        (‖left.1 p‖ *
            (sobolevAmplitudeAtOrder order (k - p) * ‖right.1 (k - p)‖) +
          (sobolevAmplitudeAtOrder order p * ‖left.1 p‖) *
            ‖right.1 (k - p)‖) :=
      hweightedPlain.tsum_le_tsum hterm hright
    _ = scalarSobolevProductEnvelope order horder left right k := by
      let leftThree := restrictCoefficientsToThree order horder left
      let rightThree := restrictCoefficientsToThree order horder right
      change _ = (2 : ℝ) ^ order *
        (realL1L2FourierConvolution (absoluteCoefficient leftThree)
            (weightedAbsoluteCoefficientAtOrder order right) k +
          realL1L2FourierConvolution (absoluteCoefficient rightThree)
            (weightedAbsoluteCoefficientAtOrder order left) k)
      rw [tsum_mul_left, hfirst.tsum_add hsecond,
        realL1L2FourierConvolution_apply
          (summable_norm_absoluteCoefficient leftThree),
        realL1L2FourierConvolution_apply
          (summable_norm_absoluteCoefficient rightThree)]
      simp only [absoluteCoefficient, weightedAbsoluteCoefficientAtOrder]
      congr 1
      congr 1
      let reflected : SpatialFrequency ≃ SpatialFrequency := Equiv.subLeft k
      let reflectedTerm : SpatialFrequency → ℝ := fun q ↦
        ‖right.1 q‖ *
          (sobolevAmplitudeAtOrder order (k - q) * ‖left.1 (k - q)‖)
      calc
        (∑' p, (sobolevAmplitudeAtOrder order p * ‖left.1 p‖) *
            ‖right.1 (k - p)‖) =
            ∑' p, reflectedTerm (reflected p) := by
          apply tsum_congr
          intro p
          have hcancel : k - (k - p) = p := by abel
          simp only [reflectedTerm, reflected, Equiv.subLeft_apply, hcancel]
          ring
        _ = ∑' q, reflectedTerm q := reflected.tsum_eq reflectedTerm
        _ = ∑' q, ‖right.1 q‖ *
            (sobolevAmplitudeAtOrder order (k - q) * ‖left.1 (k - q)‖) := rfl

/-- Scalar Fourier multiplication closes on every exact order-`m` coefficient carrier for
`m ≥ 3`. -/
def scalarSobolevProduct
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) :
    PeriodicSobolevCoefficients order :=
  ⟨scalarSobolevProductConvolution order horder left right, by
    let envelope := scalarSobolevProductEnvelope order horder left right
    have henvelopeSq : Summable fun k ↦ (envelope k) ^ 2 := by
      have h := (lp.memℓp envelope).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa using h
    refine Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg order k) (sq_nonneg _))
      (fun k ↦ ?_) henvelopeSq
    have hbound :=
      norm_sobolevAmplitudeAtOrder_mul_scalarSobolevProductConvolution_le_envelope
        order horder left right k
    have henvelopeNonneg := scalarSobolevProductEnvelope_nonneg
      order horder left right k
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    calc
      periodicSobolevWeight order k *
          ‖scalarSobolevProductConvolution order horder left right k‖ ^ 2 =
          ‖(sobolevAmplitudeAtOrder order k : ℂ) *
            scalarSobolevProductConvolution order horder left right k‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sobolevAmplitudeAtOrder_nonneg order k), mul_pow,
          sobolevAmplitudeAtOrder_sq]
      _ ≤ envelope k ^ 2 := hsquare⟩

/-- Exact convolution lineage inside the higher-order product carrier. -/
theorem scalarSobolevProduct_apply
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    (scalarSobolevProduct order horder left right).1 k =
      ∑' p, left.1 p * right.1 (k - p) :=
  scalarSobolevProductConvolution_apply order horder left right k

/-! ## Quantitative tame scalar estimate -/

/-- Young's inequality bounds the complete envelope by the two possible placements of the
high-order norm. -/
theorem norm_scalarSobolevProductEnvelope_le_l1
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) :
    ‖scalarSobolevProductEnvelope order horder left right‖ ≤
      (2 : ℝ) ^ order *
        (coefficientL1Mass (restrictCoefficientsToThree order horder left) *
            periodicSobolevCoefficientNorm order right +
          coefficientL1Mass (restrictCoefficientsToThree order horder right) *
            periodicSobolevCoefficientNorm order left) := by
  let leftThree := restrictCoefficientsToThree order horder left
  let rightThree := restrictCoefficientsToThree order horder right
  let first := realL1L2FourierConvolution (absoluteCoefficient leftThree)
    (weightedAbsoluteCoefficientAtOrder order right)
  let second := realL1L2FourierConvolution (absoluteCoefficient rightThree)
    (weightedAbsoluteCoefficientAtOrder order left)
  have hfirst : ‖first‖ ≤
      coefficientL1Mass leftThree * periodicSobolevCoefficientNorm order right := by
    simpa [first, coefficientL1Mass, periodicSobolevCoefficientNorm,
      absoluteCoefficient] using
      norm_realL1L2FourierConvolution_le
        (summable_norm_absoluteCoefficient leftThree)
        (weightedAbsoluteCoefficientAtOrder order right)
  have hsecond : ‖second‖ ≤
      coefficientL1Mass rightThree * periodicSobolevCoefficientNorm order left := by
    simpa [second, coefficientL1Mass, periodicSobolevCoefficientNorm,
      absoluteCoefficient] using
      norm_realL1L2FourierConvolution_le
        (summable_norm_absoluteCoefficient rightThree)
        (weightedAbsoluteCoefficientAtOrder order left)
  calc
    ‖scalarSobolevProductEnvelope order horder left right‖ =
        (2 : ℝ) ^ order * ‖first + second‖ := by
      change ‖((2 : ℝ) ^ order) • (first + second)‖ = _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (by norm_num) order)]
    _ ≤ (2 : ℝ) ^ order * (‖first‖ + ‖second‖) := by
      gcongr
      exact norm_add_le first second
    _ ≤ (2 : ℝ) ^ order *
        (coefficientL1Mass leftThree * periodicSobolevCoefficientNorm order right +
          coefficientL1Mass rightThree * periodicSobolevCoefficientNorm order left) := by
      gcongr

/-- The generic complete envelope satisfies the exact low-high tame estimate. -/
theorem norm_scalarSobolevProductEnvelope_le_tame
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) :
    ‖scalarSobolevProductEnvelope order horder left right‖ ≤
      (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
        (periodicH3CoefficientNorm
              (restrictCoefficientsToThree order horder left) *
            periodicSobolevCoefficientNorm order right +
          periodicH3CoefficientNorm
              (restrictCoefficientsToThree order horder right) *
            periodicSobolevCoefficientNorm order left) := by
  let leftThree := restrictCoefficientsToThree order horder left
  let rightThree := restrictCoefficientsToThree order horder right
  have hbase := norm_scalarSobolevProductEnvelope_le_l1
    order horder left right
  have hleft := coefficientL1Mass_le_periodicH3EmbeddingConstant_mul leftThree
  have hright := coefficientL1Mass_le_periodicH3EmbeddingConstant_mul rightThree
  have hC : 0 ≤ (2 : ℝ) ^ order := pow_nonneg (by norm_num) order
  have hE := periodicH3EmbeddingConstant_nonneg
  have hleftLow := periodicH3CoefficientNorm_nonneg leftThree
  have hrightLow := periodicH3CoefficientNorm_nonneg rightThree
  have hleftHigh := periodicSobolevCoefficientNorm_nonneg order left
  have hrightHigh := periodicSobolevCoefficientNorm_nonneg order right
  calc
    ‖scalarSobolevProductEnvelope order horder left right‖ ≤
        (2 : ℝ) ^ order *
          (coefficientL1Mass leftThree * periodicSobolevCoefficientNorm order right +
            coefficientL1Mass rightThree * periodicSobolevCoefficientNorm order left) := hbase
    _ ≤ (2 : ℝ) ^ order *
        ((periodicH3EmbeddingConstant * periodicH3CoefficientNorm leftThree) *
            periodicSobolevCoefficientNorm order right +
          (periodicH3EmbeddingConstant * periodicH3CoefficientNorm rightThree) *
            periodicSobolevCoefficientNorm order left) := by
      gcongr
    _ = (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
        (periodicH3CoefficientNorm leftThree *
            periodicSobolevCoefficientNorm order right +
          periodicH3CoefficientNorm rightThree *
            periodicSobolevCoefficientNorm order left) := by ring

private theorem norm_weightedScalarSobolevProduct_apply_le_envelope
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    ‖weightedAbsoluteCoefficientAtOrder order
        (scalarSobolevProduct order horder left right) k‖ ≤
      ‖scalarSobolevProductEnvelope order horder left right k‖ := by
  have hbound :=
    norm_sobolevAmplitudeAtOrder_mul_scalarSobolevProductConvolution_le_envelope
      order horder left right k
  have hleftNonneg :
      0 ≤ sobolevAmplitudeAtOrder order k *
        ‖scalarSobolevProductConvolution order horder left right k‖ :=
    mul_nonneg (sobolevAmplitudeAtOrder_nonneg order k) (norm_nonneg _)
  have hrightNonneg := scalarSobolevProductEnvelope_nonneg
    order horder left right k
  simpa only [weightedAbsoluteCoefficientAtOrder, scalarSobolevProduct,
    Real.norm_eq_abs, abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg,
    norm_mul, Complex.norm_real,
    abs_of_nonneg (sobolevAmplitudeAtOrder_nonneg order k), abs_norm] using hbound

/-- The weighted order-`m` norm of the complete product is no larger than its Young envelope. -/
theorem periodicSobolevCoefficientNorm_scalarSobolevProduct_le_envelope
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) :
    periodicSobolevCoefficientNorm order
        (scalarSobolevProduct order horder left right) ≤
      ‖scalarSobolevProductEnvelope order horder left right‖ := by
  let product := weightedAbsoluteCoefficientAtOrder order
    (scalarSobolevProduct order horder left right)
  let envelope := scalarSobolevProductEnvelope order horder left right
  have hproductSummable : Summable fun k ↦ ‖product k‖ ^ 2 := by
    have h := (lp.memℓp product).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have henvelopeSummable : Summable fun k ↦ ‖envelope k‖ ^ 2 := by
    have h := (lp.memℓp envelope).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hpoint : ∀ k, ‖product k‖ ^ 2 ≤ ‖envelope k‖ ^ 2 := by
    intro k
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_weightedScalarSobolevProduct_apply_le_envelope
        order horder left right k) 2
  have hsum : (∑' k, ‖product k‖ ^ 2) ≤ ∑' k, ‖envelope k‖ ^ 2 :=
    hproductSummable.tsum_le_tsum hpoint henvelopeSummable
  have hproductNorm : (∑' k, ‖product k‖ ^ 2) = ‖product‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) product
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  have henvelopeNorm : (∑' k, ‖envelope k‖ ^ 2) = ‖envelope‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) envelope
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  unfold periodicSobolevCoefficientNorm
  change ‖product‖ ≤ ‖envelope‖
  rw [hproductNorm, henvelopeNorm] at hsum
  nlinarith [norm_nonneg product, norm_nonneg envelope]

/-- Coefficient-level tame algebra estimate at every natural order `m ≥ 3`. -/
theorem periodicSobolevCoefficientNorm_scalarSobolevProduct_le_tame
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicSobolevCoefficients order) :
    periodicSobolevCoefficientNorm order
        (scalarSobolevProduct order horder left right) ≤
      (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
        (periodicH3CoefficientNorm
              (restrictCoefficientsToThree order horder left) *
            periodicSobolevCoefficientNorm order right +
          periodicH3CoefficientNorm
              (restrictCoefficientsToThree order horder right) *
            periodicSobolevCoefficientNorm order left) :=
  (periodicSobolevCoefficientNorm_scalarSobolevProduct_le_envelope
      order horder left right).trans
    (norm_scalarSobolevProductEnvelope_le_tame order horder left right)

/-! ## Native scalar tame passage -/

/-- Restricting an unweighted native state and then observing its coefficients is exactly the
same occurrence as restricting the native weighted state first. -/
theorem restrictCoefficientsToThree_weightedSobolevCoefficients
    (order : ℕ) (horder : 3 ≤ order)
    (state : PeriodicWeightedSobolev order) :
    restrictCoefficientsToThree order horder
        (weightedSobolevCoefficients order state) =
      weightedSobolevCoefficients 3
        (periodicWeightedSobolevRestrict 3 order horder state) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [restrictCoefficientsToThree_apply,
    weightedSobolevCoefficients_restrict_apply]

/-- Multiply two native complete order-`m` states without truncating their coefficient
population. -/
def periodicWeightedSobolevProduct
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicWeightedSobolev order) :
    PeriodicWeightedSobolev order :=
  coefficientWeightedRealization order
    (scalarSobolevProduct order horder
      (weightedSobolevCoefficients order left)
      (weightedSobolevCoefficients order right))

/-- Exact unweighted coefficient law of the native higher-order product. -/
theorem weightedSobolevCoefficients_periodicWeightedSobolevProduct_apply
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicWeightedSobolev order) (k : SpatialFrequency) :
    (weightedSobolevCoefficients order
      (periodicWeightedSobolevProduct order horder left right)).1 k =
      ∑' p,
        (weightedSobolevCoefficients order left).1 p *
          (weightedSobolevCoefficients order right).1 (k - p) := by
  rw [periodicWeightedSobolevProduct,
    weightedSobolevCoefficients_coefficientWeightedRealization,
    scalarSobolevProduct_apply]

/-- Native tame product estimate.  The low norms are the exact high-to-`H³` restrictions, while
the full order-`m` norm lands on the opposite factor. -/
theorem norm_periodicWeightedSobolevProduct_le_tame
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicWeightedSobolev order) :
    ‖periodicWeightedSobolevProduct order horder left right‖ ≤
      (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
        (‖periodicWeightedSobolevRestrict 3 order horder left‖ * ‖right‖ +
          ‖periodicWeightedSobolevRestrict 3 order horder right‖ * ‖left‖) := by
  change ‖coefficientWeightedRealization order
      (scalarSobolevProduct order horder
        (weightedSobolevCoefficients order left)
        (weightedSobolevCoefficients order right))‖ ≤ _
  rw [← periodicSobolevCoefficientNorm_eq_nativeNorm]
  have hbase := periodicSobolevCoefficientNorm_scalarSobolevProduct_le_tame
    order horder (weightedSobolevCoefficients order left)
      (weightedSobolevCoefficients order right)
  rw [periodicSobolevCoefficientNorm_weightedSobolevCoefficients,
    periodicSobolevCoefficientNorm_weightedSobolevCoefficients] at hbase
  rw [restrictCoefficientsToThree_weightedSobolevCoefficients,
    restrictCoefficientsToThree_weightedSobolevCoefficients,
    periodicH3CoefficientNorm_weightedSobolevCoefficients,
    periodicH3CoefficientNorm_weightedSobolevCoefficients] at hbase
  exact hbase

/-! ## Spending one exact derivative at an arbitrary positive order -/

/-- One coordinate derivative symbol consumes at most one adjacent Sobolev weight. -/
theorem periodicSobolevWeight_pred_mul_coordinate_symbol_sq_le
    (order : ℕ) (hpositive : 1 ≤ order)
    (coordinate : Fin 3) (k : SpatialFrequency) :
    periodicSobolevWeight (order - 1) k *
        ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) ≤
      periodicSobolevWeight order k := by
  have hcoordinate : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ coordinate)
  have hsymbol :
      (2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2 ≤
        torusStokesEigenvalue k := by
    rw [torusStokesEigenvalue]
    exact mul_le_mul_of_nonneg_left hcoordinate (sq_nonneg (2 * Real.pi))
  have hbase : 0 ≤ 1 + torusStokesEigenvalue k :=
    add_nonneg zero_le_one (torusStokesEigenvalue_nonneg k)
  unfold periodicSobolevWeight
  calc
    (1 + torusStokesEigenvalue k) ^ (order - 1) *
        ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) ≤
        (1 + torusStokesEigenvalue k) ^ (order - 1) *
          torusStokesEigenvalue k :=
      mul_le_mul_of_nonneg_left hsymbol (pow_nonneg hbase _)
    _ ≤ (1 + torusStokesEigenvalue k) ^ (order - 1) *
        (1 + torusStokesEigenvalue k) :=
      mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left zero_le_one) (pow_nonneg hbase _)
    _ = (1 + torusStokesEigenvalue k) ^ order := by
      rw [← pow_succ, Nat.sub_add_cancel hpositive]

private theorem norm_periodicSobolevDerivativeValue_sq
    {order : ℕ} (coordinate : Fin 3)
    (coeff : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k‖ ^ 2 =
      ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
    Complex.norm_I, Complex.norm_intCast, mul_one]
  rw [abs_of_pos Real.pi_pos]
  ring_nf
  rw [sq_abs]
  ring

private theorem summable_periodicSobolevDerivative_weighted_pred
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (coeff : PeriodicSobolevCoefficients order) :
    Summable fun k ↦ periodicSobolevWeight (order - 1) k *
      ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg (order - 1) k) (sq_nonneg _))
    (fun k ↦ ?_) coeff.2
  rw [norm_periodicSobolevDerivativeValue_sq]
  calc
    periodicSobolevWeight (order - 1) k *
        (((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2) =
        (periodicSobolevWeight (order - 1) k *
          ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2)) * ‖coeff.1 k‖ ^ 2 := by
      ring
    _ ≤ periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (periodicSobolevWeight_pred_mul_coordinate_symbol_sq_le
          order hpositive coordinate k) (sq_nonneg _)

private theorem summable_periodicSobolevDerivative_sq
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (coeff : PeriodicSobolevCoefficients order) :
    Summable fun k ↦
      ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k‖ ^ 2 := by
  have hweighted := summable_periodicSobolevDerivative_weighted_pred
    order hpositive coordinate coeff
  refine Summable.of_nonneg_of_le (fun k ↦ sq_nonneg _) (fun k ↦ ?_) hweighted
  calc
    ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k‖ ^ 2 =
        1 * ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
          coeff.1 k‖ ^ 2 := by ring
    _ ≤ periodicSobolevWeight (order - 1) k *
        ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
          coeff.1 k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (one_le_periodicSobolevWeight (order - 1) k) (sq_nonneg _)

/-- The complete unweighted derivative population in its underlying Fourier `ℓ²` carrier. -/
def periodicSobolevDerivativeFourier
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (coeff : PeriodicSobolevCoefficients order) : PeriodicFourierL2 :=
  ⟨fun k ↦ (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two] using
      summable_periodicSobolevDerivative_sq order hpositive coordinate coeff⟩

/-- One coordinate derivative as an honest `H^m → H^(m-1)` coefficient passage. -/
def periodicSobolevDerivativeIntoPred
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (coeff : PeriodicSobolevCoefficients order) :
    PeriodicSobolevCoefficients (order - 1) :=
  ⟨periodicSobolevDerivativeFourier order hpositive coordinate coeff, by
    simpa only [periodicSobolevDerivativeFourier] using
      summable_periodicSobolevDerivative_weighted_pred
        order hpositive coordinate coeff⟩

@[simp]
theorem periodicSobolevDerivativeIntoPred_apply
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (coeff : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    (periodicSobolevDerivativeIntoPred order hpositive coordinate coeff).1 k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k :=
  rfl

private theorem periodicRealFourierL2_norm_le_of_pointwise_sq_le
    (left right : PeriodicRealFourierL2)
    (hpoint : ∀ k, ‖left k‖ ^ 2 ≤ ‖right k‖ ^ 2) :
    ‖left‖ ≤ ‖right‖ := by
  have hleftSummable : Summable fun k ↦ ‖left k‖ ^ 2 := by
    have h := (lp.memℓp left).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hrightSummable : Summable fun k ↦ ‖right k‖ ^ 2 := by
    have h := (lp.memℓp right).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hsum : (∑' k, ‖left k‖ ^ 2) ≤ ∑' k, ‖right k‖ ^ 2 :=
    hleftSummable.tsum_le_tsum hpoint hrightSummable
  have hleftNorm : (∑' k, ‖left k‖ ^ 2) = ‖left‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) left
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  have hrightNorm : (∑' k, ‖right k‖ ^ 2) = ‖right‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) right
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  rw [hleftNorm, hrightNorm] at hsum
  nlinarith [norm_nonneg left, norm_nonneg right]

private theorem norm_weightedAbsoluteCoefficientAtOrder_apply_sq
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order)
    (k : SpatialFrequency) :
    ‖weightedAbsoluteCoefficientAtOrder order coeff k‖ ^ 2 =
      periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2 := by
  simp only [weightedAbsoluteCoefficientAtOrder, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (sobolevAmplitudeAtOrder_nonneg order k) (norm_nonneg _)),
    mul_pow, sobolevAmplitudeAtOrder_sq]

/-- Spending one coordinate derivative has norm at most one across adjacent exact Sobolev
scales. -/
theorem periodicSobolevCoefficientNorm_derivativeIntoPred_le
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (coeff : PeriodicSobolevCoefficients order) :
    periodicSobolevCoefficientNorm (order - 1)
        (periodicSobolevDerivativeIntoPred order hpositive coordinate coeff) ≤
      periodicSobolevCoefficientNorm order coeff := by
  unfold periodicSobolevCoefficientNorm
  apply periodicRealFourierL2_norm_le_of_pointwise_sq_le
  intro k
  rw [norm_weightedAbsoluteCoefficientAtOrder_apply_sq,
    norm_weightedAbsoluteCoefficientAtOrder_apply_sq,
    periodicSobolevDerivativeIntoPred_apply,
    norm_periodicSobolevDerivativeValue_sq]
  calc
    periodicSobolevWeight (order - 1) k *
        (((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2) =
        (periodicSobolevWeight (order - 1) k *
          ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2)) * ‖coeff.1 k‖ ^ 2 := by
      ring
    _ ≤ periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (periodicSobolevWeight_pred_mul_coordinate_symbol_sq_le
          order hpositive coordinate k) (sq_nonneg _)

/-- The adjacent derivative on the native complete weighted carrier. -/
def periodicWeightedSobolevDerivativeIntoPred
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (state : PeriodicWeightedSobolev order) :
    PeriodicWeightedSobolev (order - 1) :=
  coefficientWeightedRealization (order - 1)
    (periodicSobolevDerivativeIntoPred order hpositive coordinate
      (weightedSobolevCoefficients order state))

/-- Exact unweighted multiplier law of the native adjacent derivative. -/
theorem weightedSobolevCoefficients_periodicWeightedSobolevDerivativeIntoPred_apply
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (state : PeriodicWeightedSobolev order) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (order - 1)
      (periodicWeightedSobolevDerivativeIntoPred
        order hpositive coordinate state)).1 k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (weightedSobolevCoefficients order state).1 k := by
  rw [periodicWeightedSobolevDerivativeIntoPred,
    weightedSobolevCoefficients_coefficientWeightedRealization,
    periodicSobolevDerivativeIntoPred_apply]

/-- The native adjacent derivative is a contraction. -/
theorem norm_periodicWeightedSobolevDerivativeIntoPred_le
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (state : PeriodicWeightedSobolev order) :
    ‖periodicWeightedSobolevDerivativeIntoPred order hpositive coordinate state‖ ≤
      ‖state‖ := by
  change ‖coefficientWeightedRealization (order - 1)
      (periodicSobolevDerivativeIntoPred order hpositive coordinate
        (weightedSobolevCoefficients order state))‖ ≤ _
  rw [← periodicSobolevCoefficientNorm_eq_nativeNorm,
    ← periodicSobolevCoefficientNorm_weightedSobolevCoefficients order state]
  exact periodicSobolevCoefficientNorm_derivativeIntoPred_le
    order hpositive coordinate (weightedSobolevCoefficients order state)

/-! ## One native divergence face -/

/-- One exact native face `∂j(left · right)` from `H^m × H^m` into `H^(m-1)`. -/
def periodicWeightedSobolevDivergenceProduct
    (order : ℕ) (horder : 3 ≤ order) (coordinate : Fin 3)
    (left right : PeriodicWeightedSobolev order) :
    PeriodicWeightedSobolev (order - 1) :=
  periodicWeightedSobolevDerivativeIntoPred order (by omega) coordinate
    (periodicWeightedSobolevProduct order horder left right)

/-- Exact complete-lattice coefficient law for one native higher-order divergence face. -/
theorem weightedSobolevCoefficients_periodicWeightedSobolevDivergenceProduct_apply
    (order : ℕ) (horder : 3 ≤ order) (coordinate : Fin 3)
    (left right : PeriodicWeightedSobolev order) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (order - 1)
      (periodicWeightedSobolevDivergenceProduct
        order horder coordinate left right)).1 k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p,
          (weightedSobolevCoefficients order left).1 p *
            (weightedSobolevCoefficients order right).1 (k - p)) := by
  rw [periodicWeightedSobolevDivergenceProduct,
    weightedSobolevCoefficients_periodicWeightedSobolevDerivativeIntoPred_apply,
    weightedSobolevCoefficients_periodicWeightedSobolevProduct_apply]

/-- One native divergence face inherits the exact mixed tame estimate. -/
theorem norm_periodicWeightedSobolevDivergenceProduct_le_tame
    (order : ℕ) (horder : 3 ≤ order) (coordinate : Fin 3)
    (left right : PeriodicWeightedSobolev order) :
    ‖periodicWeightedSobolevDivergenceProduct
        order horder coordinate left right‖ ≤
      (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
        (‖periodicWeightedSobolevRestrict 3 order horder left‖ * ‖right‖ +
          ‖periodicWeightedSobolevRestrict 3 order horder right‖ * ‖left‖) :=
  (norm_periodicWeightedSobolevDerivativeIntoPred_le order (by omega) coordinate
      (periodicWeightedSobolevProduct order horder left right)).trans
    (norm_periodicWeightedSobolevProduct_le_tame order horder left right)

/-! ## Three-face native divergence assembly -/

/-- Componentwise exact restriction of a native vector state to its order-three receiver. -/
def periodicVectorWeightedRestrictToThree
    (order : ℕ) (horder : 3 ≤ order)
    (state : PeriodicVectorWeightedSobolev order) :
    PeriodicVectorWeightedSobolev 3 :=
  periodicVectorWeightedSobolevRestrictCLM 3 order horder state

@[simp]
theorem periodicVectorWeightedRestrictToThree_apply
    (order : ℕ) (horder : 3 ≤ order)
    (state : PeriodicVectorWeightedSobolev order) (component : Fin 3) :
    periodicVectorWeightedRestrictToThree order horder state component =
      periodicWeightedSobolevRestrict 3 order horder (state component) :=
  rfl

/-- The complete native coefficient population of
`output ↦ ∑ j, ∂j(advecting_j transported_output)` at arbitrary order `m ≥ 3`. -/
def periodicVectorWeightedDivergenceConvolution
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    PeriodicVectorWeightedSobolev (order - 1) :=
  fun output ↦ ∑ coordinate : Fin 3,
    periodicWeightedSobolevDivergenceProduct order horder coordinate
      (advecting coordinate) (transported output)

/-- Exact coefficient lineage of all three divergence faces; no word or component is dropped. -/
theorem weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order)
    (output : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (order - 1)
      (periodicVectorWeightedDivergenceConvolution
        order horder advecting transported output)).1 k =
      ∑ coordinate : Fin 3,
        (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
          (∑' p,
            (weightedSobolevCoefficients order (advecting coordinate)).1 p *
              (weightedSobolevCoefficients order (transported output)).1 (k - p)) := by
  change ((((Real.sqrt (periodicSobolevWeight (order - 1) k))⁻¹ : ℝ) : ℂ) *
      (∑ coordinate : Fin 3,
        periodicWeightedSobolevDivergenceProduct order horder coordinate
          (advecting coordinate) (transported output)) k) = _
  simp only [lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact weightedSobolevCoefficients_periodicWeightedSobolevDivergenceProduct_apply
    order horder coordinate (advecting coordinate) (transported output) k

/-- The assembled native divergence population satisfies the same mixed tame estimate, with the
finite three-face constant retained explicitly. -/
theorem norm_periodicVectorWeightedDivergenceConvolution_le_tame
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    ‖periodicVectorWeightedDivergenceConvolution
        order horder advecting transported‖ ≤
      (3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
            ‖transported‖ +
          ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
            ‖advecting‖) := by
  have hconstant :
      0 ≤ 3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant :=
    mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) order))
      periodicH3EmbeddingConstant_nonneg
  have hcross : 0 ≤
      ‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
          ‖transported‖ +
        ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
          ‖advecting‖ := by positivity
  have hrightNonneg : 0 ≤
      (3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
            ‖transported‖ +
          ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
            ‖advecting‖) :=
    mul_nonneg hconstant hcross
  rw [pi_norm_le_iff_of_nonneg hrightNonneg]
  intro output
  calc
    ‖periodicVectorWeightedDivergenceConvolution
        order horder advecting transported output‖ ≤
        ∑ coordinate : Fin 3,
          ‖periodicWeightedSobolevDivergenceProduct order horder coordinate
            (advecting coordinate) (transported output)‖ := by
      unfold periodicVectorWeightedDivergenceConvolution
      exact norm_sum_le _ _
    _ ≤ ∑ _coordinate : Fin 3,
        (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
          (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
              ‖transported‖ +
            ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
              ‖advecting‖) := by
      apply Finset.sum_le_sum
      intro coordinate _
      calc
        ‖periodicWeightedSobolevDivergenceProduct order horder coordinate
            (advecting coordinate) (transported output)‖ ≤
            (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
              (‖periodicWeightedSobolevRestrict 3 order horder
                    (advecting coordinate)‖ * ‖transported output‖ +
                ‖periodicWeightedSobolevRestrict 3 order horder
                    (transported output)‖ * ‖advecting coordinate‖) :=
          norm_periodicWeightedSobolevDivergenceProduct_le_tame
            order horder coordinate (advecting coordinate) (transported output)
        _ ≤ (2 : ℝ) ^ order * periodicH3EmbeddingConstant *
            (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
                ‖transported‖ +
              ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
                ‖advecting‖) := by
          gcongr
          · exact mul_nonneg (pow_nonneg (by norm_num) order)
              periodicH3EmbeddingConstant_nonneg
          · simpa only [periodicVectorWeightedRestrictToThree_apply] using
              norm_le_pi_norm
                (periodicVectorWeightedRestrictToThree order horder advecting) coordinate
          · exact norm_le_pi_norm transported output
          · simpa only [periodicVectorWeightedRestrictToThree_apply] using
              norm_le_pi_norm
                (periodicVectorWeightedRestrictToThree order horder transported) output
          · exact norm_le_pi_norm advecting coordinate
    _ = (3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
            ‖transported‖ +
          ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
            ‖advecting‖) := by
      simp only [Fin.sum_univ_three]
      ring

/-! ## Same-order native Leray projection -/

private theorem summable_periodicVectorWeighted_sq
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) :
    Summable fun k ↦ ∑ component : Fin 3, ‖state component k‖ ^ 2 := by
  have hcomponent (component : Fin 3) :
      Summable fun k ↦ ‖state component k‖ ^ 2 := by
    have h := (lp.memℓp (state component)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  simpa [Fin.sum_univ_succ, add_assoc] using
    (hcomponent 0).add ((hcomponent 1).add (hcomponent 2))

/-- One output component of the exact modewise Leray projection, acting directly on a native
weighted state.  The common scalar Sobolev weight commutes with the projection. -/
def periodicVectorWeightedLerayProjectComponent
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) (output : Fin 3) :
    PeriodicWeightedSobolev order :=
  ⟨fun k ↦ lerayProjectMode k (fun component ↦ state component k) output, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hsource := summable_periodicVectorWeighted_sq order state
    have hbound := hsource.mul_left 12
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) hbound
    simpa only [Real.rpow_two] using
      norm_lerayProjectMode_coordinate_sq_le k
        (fun component ↦ state component k) output⟩

@[simp]
theorem periodicVectorWeightedLerayProjectComponent_apply
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order)
    (output : Fin 3) (k : SpatialFrequency) :
    periodicVectorWeightedLerayProjectComponent order state output k =
      lerayProjectMode k (fun component ↦ state component k) output :=
  rfl

/-- Native modewise Leray projection at every exact Sobolev order. -/
def periodicVectorWeightedLerayProject
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) :
    PeriodicVectorWeightedSobolev order :=
  fun output ↦ periodicVectorWeightedLerayProjectComponent order state output

private theorem norm_periodicVectorWeightedLerayProjectComponent_le
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) (output : Fin 3) :
    ‖periodicVectorWeightedLerayProjectComponent order state output‖ ≤
      6 * ‖state‖ := by
  let projected := periodicVectorWeightedLerayProjectComponent order state output
  have hprojectedSummable : Summable fun k ↦ ‖projected k‖ ^ 2 := by
    have h := (lp.memℓp projected).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hsource := summable_periodicVectorWeighted_sq order state
  have hbound := hsource.mul_left 12
  have hpoint : ∀ k, ‖projected k‖ ^ 2 ≤
      12 * ∑ component : Fin 3, ‖state component k‖ ^ 2 := by
    intro k
    exact norm_lerayProjectMode_coordinate_sq_le k
      (fun component ↦ state component k) output
  have hsum : (∑' k, ‖projected k‖ ^ 2) ≤
      ∑' k, 12 * ∑ component : Fin 3, ‖state component k‖ ^ 2 :=
    hprojectedSummable.tsum_le_tsum hpoint hbound
  have hprojectedNorm : (∑' k, ‖projected k‖ ^ 2) = ‖projected‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) projected
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  have hcomponent (component : Fin 3) :
      Summable fun k ↦ ‖state component k‖ ^ 2 := by
    have h := (lp.memℓp (state component)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hinterchange :
      (∑' k, ∑ component : Fin 3, ‖state component k‖ ^ 2) =
        ∑ component : Fin 3, ∑' k, ‖state component k‖ ^ 2 :=
    Summable.tsum_finsetSum (s := Finset.univ) (fun component _ ↦ hcomponent component)
  have hcomponentNorm (component : Fin 3) :
      (∑' k, ‖state component k‖ ^ 2) = ‖state component‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (state component)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  have hfinite :
      (∑ component : Fin 3, ‖state component‖ ^ 2) ≤ 3 * ‖state‖ ^ 2 := by
    calc
      (∑ component : Fin 3, ‖state component‖ ^ 2) ≤
          ∑ _component : Fin 3, ‖state‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro component _
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_le_pi_norm state component) 2
      _ = 3 * ‖state‖ ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring
  have hsquare : ‖projected‖ ^ 2 ≤ (6 * ‖state‖) ^ 2 := by
    rw [← hprojectedNorm]
    calc
      (∑' k, ‖projected k‖ ^ 2) ≤
          ∑' k, 12 * ∑ component : Fin 3, ‖state component k‖ ^ 2 := hsum
      _ = 12 * (∑' k, ∑ component : Fin 3, ‖state component k‖ ^ 2) := by
        rw [hsource.tsum_mul_left]
      _ = 12 * (∑ component : Fin 3,
          ∑' k, ‖state component k‖ ^ 2) := by rw [hinterchange]
      _ = 12 * (∑ component : Fin 3, ‖state component‖ ^ 2) := by
        apply congrArg
        apply Finset.sum_congr rfl
        intro component _
        exact hcomponentNorm component
      _ ≤ 12 * (3 * ‖state‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hfinite (by norm_num)
      _ = (6 * ‖state‖) ^ 2 := by ring
  nlinarith [norm_nonneg projected, norm_nonneg state]

/-- The generic native Leray face has explicit coarse operator constant six in the repository's
componentwise product norm. -/
theorem norm_periodicVectorWeightedLerayProject_le
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) :
    ‖periodicVectorWeightedLerayProject order state‖ ≤ 6 * ‖state‖ := by
  have hright : 0 ≤ 6 * ‖state‖ := by positivity
  rw [pi_norm_le_iff_of_nonneg hright]
  intro output
  exact norm_periodicVectorWeightedLerayProjectComponent_le order state output

private theorem lerayProjectMode_smul_native
    (c : ℂ) (k : SpatialFrequency) (mode : ComplexVector) :
    lerayProjectMode k (c • mode) = c • lerayProjectMode k mode := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [lerayProjectMode, if_neg hk, lerayProjectMode, if_neg hk]
    ext output
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, complexDot,
      dotProduct_smul]
    ring

/-- Forget only the native scalar weight while retaining every mode and component. -/
def nativeVectorUnderlyingAtOrder
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) :
    PeriodicVectorFourierL2 :=
  fun component ↦ weightedSobolevRawCoefficients order (state component)

/-- Unweighting commutes exactly with the same-order native Leray projection. -/
theorem vectorCoefficientAt_nativeVectorUnderlyingAtOrder_lerayProject
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) :
    vectorCoefficientAt
        (nativeVectorUnderlyingAtOrder order
          (periodicVectorWeightedLerayProject order state)) k =
      lerayProjectMode k
        (vectorCoefficientAt (nativeVectorUnderlyingAtOrder order state) k) := by
  funext output
  let scale : ℂ :=
    (((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ)
  have hsmul := congrFun
    (lerayProjectMode_smul_native scale k (fun component ↦ state component k)) output
  change scale * lerayProjectMode k (fun component ↦ state component k) output =
    lerayProjectMode k (fun component ↦ scale * state component k) output
  simpa only [Pi.smul_apply, smul_eq_mul] using hsmul.symm

/-- Same-order native Leray projection returns an exactly modewise divergence-free unweighted
population. -/
theorem periodicVectorWeightedLerayProject_divergenceFree
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) :
    IsModewiseDivergenceFree
      (nativeVectorUnderlyingAtOrder order
        (periodicVectorWeightedLerayProject order state)) := by
  intro k
  rw [vectorCoefficientAt_nativeVectorUnderlyingAtOrder_lerayProject]
  exact complexDot_lerayProjectMode_eq_zero k _

/-! ## The generic native Leray-divergence passage -/

/-- The exact higher-order quadratic population: assemble every divergence face, then apply the
modewise Leray receiver at the same target order. -/
def periodicVectorWeightedLerayDivergenceConvolution
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    PeriodicVectorWeightedSobolev (order - 1) :=
  periodicVectorWeightedLerayProject (order - 1)
    (periodicVectorWeightedDivergenceConvolution
      order horder advecting transported)

/-- Exact complete-mode coefficient law of the generic native Leray-divergence passage. -/
theorem vectorCoefficientAt_periodicVectorWeightedLerayDivergenceConvolution
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) :
    vectorCoefficientAt
        (nativeVectorUnderlyingAtOrder (order - 1)
          (periodicVectorWeightedLerayDivergenceConvolution
            order horder advecting transported)) k =
      lerayProjectMode k
        (fun output ↦ ∑ coordinate : Fin 3,
          (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
            (∑' p,
              (weightedSobolevCoefficients order (advecting coordinate)).1 p *
                (weightedSobolevCoefficients order
                  (transported output)).1 (k - p))) := by
  rw [periodicVectorWeightedLerayDivergenceConvolution,
    vectorCoefficientAt_nativeVectorUnderlyingAtOrder_lerayProject]
  congr 1
  funext output
  exact weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply
    order horder advecting transported output k

/-- The mixed tame native `H^m × H^m → H^(m-1)` Leray-divergence estimate.  Each low norm is the
exact high-to-`H³` restriction, not a second coefficient population. -/
theorem norm_periodicVectorWeightedLerayDivergenceConvolution_le_tame
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    ‖periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting transported‖ ≤
      (18 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
            ‖transported‖ +
          ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
            ‖advecting‖) := by
  calc
    ‖periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting transported‖ ≤
        6 * ‖periodicVectorWeightedDivergenceConvolution
          order horder advecting transported‖ :=
      norm_periodicVectorWeightedLerayProject_le (order - 1)
        (periodicVectorWeightedDivergenceConvolution
          order horder advecting transported)
    _ ≤ 6 * ((3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
            ‖transported‖ +
          ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
            ‖advecting‖)) :=
      mul_le_mul_of_nonneg_left
        (norm_periodicVectorWeightedDivergenceConvolution_le_tame
          order horder advecting transported) (by norm_num)
    _ = (18 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
            ‖transported‖ +
          ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
            ‖advecting‖) := by ring

/-- Componentwise high-to-`H³` restriction is norm-nonexpanding on the native vector carrier. -/
theorem norm_periodicVectorWeightedRestrictToThree_le
    (order : ℕ) (horder : 3 ≤ order)
    (state : PeriodicVectorWeightedSobolev order) :
    ‖periodicVectorWeightedRestrictToThree order horder state‖ ≤ ‖state‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg state)]
  intro component
  calc
    ‖periodicVectorWeightedRestrictToThree order horder state component‖ =
        ‖periodicWeightedSobolevRestrict 3 order horder (state component)‖ := rfl
    _ ≤ ‖state component‖ :=
      norm_periodicWeightedSobolevRestrict_le
        3 order horder (state component)
    _ ≤ ‖state‖ := norm_le_pi_norm state component

/-- Coarser symmetric high-high consequence of the tame estimate. -/
theorem norm_periodicVectorWeightedLerayDivergenceConvolution_le
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    ‖periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting transported‖ ≤
      (36 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        ‖advecting‖ * ‖transported‖ := by
  have hbase := norm_periodicVectorWeightedLerayDivergenceConvolution_le_tame
    order horder advecting transported
  have hu := norm_periodicVectorWeightedRestrictToThree_le
    order horder advecting
  have hv := norm_periodicVectorWeightedRestrictToThree_le
    order horder transported
  have hconstant : 0 ≤ 18 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant :=
    mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) order))
      periodicH3EmbeddingConstant_nonneg
  calc
    ‖periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting transported‖ ≤
        (18 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
          (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
              ‖transported‖ +
            ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
              ‖advecting‖) := hbase
    _ ≤ (18 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖advecting‖ * ‖transported‖ + ‖transported‖ * ‖advecting‖) := by
      gcongr
    _ = (36 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        ‖advecting‖ * ‖transported‖ := by ring

/-- The generic projected output retains the exact Fourier incompressibility constraint. -/
theorem periodicVectorWeightedLerayDivergenceConvolution_divergenceFree
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    IsModewiseDivergenceFree
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting transported)) :=
  periodicVectorWeightedLerayProject_divergenceFree (order - 1)
    (periodicVectorWeightedDivergenceConvolution
      order horder advecting transported)

section Audit

#print axioms sobolevAmplitudeAtOrder_add_le
#print axioms norm_periodicWeightedSobolevProduct_le_tame
#print axioms periodicSobolevCoefficientNorm_derivativeIntoPred_le
#print axioms norm_periodicVectorWeightedLerayDivergenceConvolution_le_tame
#print axioms norm_periodicVectorWeightedLerayDivergenceConvolution_le
#print axioms periodicVectorWeightedLerayDivergenceConvolution_divergenceFree

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
