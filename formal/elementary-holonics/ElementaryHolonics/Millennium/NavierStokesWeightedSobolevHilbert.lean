import ElementaryHolonics.Millennium.NavierStokesH2ToH3HeatSmoothing

/-!
# A complete weighted Sobolev realization

The historical `PeriodicSobolevCoefficients n` subtype records weighted summability but inherits
the unweighted Fourier topology.  A contraction argument must instead live in the norm of the
weighted coefficients themselves.

This file installs that realization without changing the coefficient ontology.  A native
weighted Sobolev state is an ordinary complete ℓ2 population whose entry at `k` is
`sqrt(weight n k) * coeff k`.  Explicit weighting and unweighting maps are mutual inverses, and
unweighting returns the existing honest Sobolev subtype.  Thus completeness comes from Mathlib's
ℓ2 Hilbert carrier rather than from an asserted property of the old subtype.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The complete native realization of scalar periodic Sobolev order `order`. -/
abbrev PeriodicWeightedSobolev (_order : ℕ) := PeriodicFourierL2

/-- Three component-addressed native weighted Sobolev populations. -/
abbrev PeriodicVectorWeightedSobolev (order : ℕ) :=
  Fin 3 → PeriodicWeightedSobolev order

/-- Every inhomogeneous periodic Sobolev weight is at least one. -/
theorem one_le_periodicSobolevWeight (order : ℕ) (k : SpatialFrequency) :
    1 ≤ periodicSobolevWeight order k := by
  unfold periodicSobolevWeight
  exact one_le_pow₀ (by linarith [torusStokesEigenvalue_nonneg k])

theorem periodicSobolevWeight_pos (order : ℕ) (k : SpatialFrequency) :
    0 < periodicSobolevWeight order k :=
  zero_lt_one.trans_le (one_le_periodicSobolevWeight order k)

private theorem norm_unweightedCoefficient_sq
    (order : ℕ) (k : SpatialFrequency) (z : ℂ) :
    ‖(((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * z‖ ^ 2 =
      (periodicSobolevWeight order k)⁻¹ * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow,
    inv_pow, Real.sq_sqrt (periodicSobolevWeight_nonneg order k)]

private theorem norm_weightedCoefficient_sq
    (order : ℕ) (k : SpatialFrequency) (z : ℂ) :
    ‖(Real.sqrt (periodicSobolevWeight order k) : ℂ) * z‖ ^ 2 =
      periodicSobolevWeight order k * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (periodicSobolevWeight_nonneg order k)]

/-! ## Unweighting into the existing coefficient carrier -/

/-- Forget the native weight by dividing each addressed coefficient by its positive square root.
The result remains in the underlying Fourier ℓ2 carrier because every weight is at least one. -/
def weightedSobolevRawCoefficients
    (order : ℕ) (state : PeriodicWeightedSobolev order) : PeriodicFourierL2 :=
  ⟨fun k ↦ (((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hstate : Summable fun k ↦ ‖state k‖ ^ 2 := by
      have h := (lp.memℓp state).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) hstate
    have hinv : (periodicSobolevWeight order k)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_periodicSobolevWeight order k)
    have hnat :
        ‖(((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k‖ ^ 2 ≤
          ‖state k‖ ^ 2 := by
      calc
        ‖(((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k‖ ^ 2 =
            (periodicSobolevWeight order k)⁻¹ * ‖state k‖ ^ 2 :=
          norm_unweightedCoefficient_sq order k (state k)
        _ ≤ ‖state k‖ ^ 2 :=
          mul_le_of_le_one_left (sq_nonneg _) hinv
    simpa only [Real.rpow_two] using hnat⟩

@[simp]
theorem weightedSobolevRawCoefficients_apply
    (order : ℕ) (state : PeriodicWeightedSobolev order) (k : SpatialFrequency) :
    weightedSobolevRawCoefficients order state k =
      (((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k :=
  rfl

/-- Unweighting returns an honest member of the pre-existing periodic Sobolev subtype. -/
def weightedSobolevCoefficients
    (order : ℕ) (state : PeriodicWeightedSobolev order) :
    PeriodicSobolevCoefficients order :=
  ⟨weightedSobolevRawCoefficients order state, by
    unfold HasPeriodicSobolevCoefficients
    have hstate : Summable fun k ↦ ‖state k‖ ^ 2 := by
      have h := (lp.memℓp state).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
    apply hstate.congr
    intro k
    rw [weightedSobolevRawCoefficients_apply, norm_unweightedCoefficient_sq]
    have hweightNe : periodicSobolevWeight order k ≠ 0 :=
      (periodicSobolevWeight_pos order k).ne'
    field_simp⟩

/-! ## Weighting an existing Sobolev population -/

/-- Apply the exact positive square-root weight, landing in the native complete Hilbert carrier. -/
def coefficientWeightedRealization
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) :
    PeriodicWeightedSobolev order :=
  ⟨fun k ↦ (Real.sqrt (periodicSobolevWeight order k) : ℂ) * coeff.1 k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    apply Summable.congr coeff.2
    intro k
    simpa only [Real.rpow_two] using
      (norm_weightedCoefficient_sq order k (coeff.1 k)).symm⟩

@[simp]
theorem coefficientWeightedRealization_apply
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    coefficientWeightedRealization order coeff k =
      (Real.sqrt (periodicSobolevWeight order k) : ℂ) * coeff.1 k :=
  rfl

/-! ## Exact reconstruction -/

/-- Weighting after unweighting returns every native complete state exactly. -/
theorem coefficientWeightedRealization_weightedSobolevCoefficients
    (order : ℕ) (state : PeriodicWeightedSobolev order) :
    coefficientWeightedRealization order (weightedSobolevCoefficients order state) = state := by
  apply Subtype.ext
  funext k
  change (Real.sqrt (periodicSobolevWeight order k) : ℂ) *
      ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k) =
    state k
  have hsqrt : Real.sqrt (periodicSobolevWeight order k) ≠ 0 :=
    (Real.sqrt_pos.2 (periodicSobolevWeight_pos order k)).ne'
  rw [← mul_assoc]
  norm_cast
  field_simp
  simp

/-- Unweighting after weighting returns every old Sobolev coefficient population exactly. -/
theorem weightedSobolevCoefficients_coefficientWeightedRealization
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) :
    weightedSobolevCoefficients order (coefficientWeightedRealization order coeff) = coeff := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      ((Real.sqrt (periodicSobolevWeight order k) : ℂ) * coeff.1 k)) = coeff.1 k
  have hsqrt : Real.sqrt (periodicSobolevWeight order k) ≠ 0 :=
    (Real.sqrt_pos.2 (periodicSobolevWeight_pos order k)).ne'
  rw [← mul_assoc]
  norm_cast
  field_simp
  simp

/-- Squaring the native norm returns exactly the complete weighted Sobolev population. -/
theorem norm_coefficientWeightedRealization_sq_eq
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) :
    ‖coefficientWeightedRealization order coeff‖ ^ 2 =
      ∑' k, periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (coefficientWeightedRealization order coeff)
  calc
    ‖coefficientWeightedRealization order coeff‖ ^ 2 =
        ∑' k, ‖coefficientWeightedRealization order coeff k‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hnorm
    _ = ∑' k, periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2 := by
      apply tsum_congr
      intro k
      exact norm_weightedCoefficient_sq order k (coeff.1 k)

section Audit

#synth CompleteSpace (PeriodicWeightedSobolev 3)
#synth CompleteSpace (PeriodicVectorWeightedSobolev 3)

#print axioms weightedSobolevCoefficients
#print axioms coefficientWeightedRealization
#print axioms coefficientWeightedRealization_weightedSobolevCoefficients
#print axioms weightedSobolevCoefficients_coefficientWeightedRealization
#print axioms norm_coefficientWeightedRealization_sq_eq

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
