import ElementaryHolonics.Millennium.NavierStokesInfiniteFourierHeatRestart

/-!
# One-step periodic heat smoothing from H² to H³

The local mild Navier--Stokes passage needs exactly one recovered derivative after the projected
quadratic term lands in `H²`.  This file applies the already proved one-order heat multiplier
estimate to data carrying the complete order-two weight.  It returns an honest order-three
coefficient population and the explicit squared estimate

`E₃(e^{νtΔ}f) ≤ (1 + (2νt)⁻¹) E₂(f)`.

No Duhamel integral, nonlinear fixed point, or local-existence conclusion is introduced here.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The exact squared constant for one recovered Sobolev order. -/
def heatOneStepSquaredConstant (nu t : ℝ) : ℝ :=
  1 + (2 * (nu * t))⁻¹

theorem heatOneStepSquaredConstant_nonneg
    {nu t : ℝ} (hviscous : 0 < nu * t) :
    0 ≤ heatOneStepSquaredConstant nu t := by
  unfold heatOneStepSquaredConstant
  positivity

/-- The order-three target weight is the order-two source weight times the one-order heat
factor. -/
theorem periodicSobolevWeight_three_mul_heat_sq_le_two
    {nu t : ℝ} (hviscous : 0 < nu * t) (k : SpatialFrequency) :
    periodicSobolevWeight 3 k * (heatStokesMultiplier nu t k) ^ 2 ≤
      heatOneStepSquaredConstant nu t * periodicSobolevWeight 2 k := by
  have hone := periodicSobolevWeight_one_mul_heat_sq_le hviscous k
  have htwo : 0 ≤ periodicSobolevWeight 2 k :=
    periodicSobolevWeight_nonneg 2 k
  calc
    periodicSobolevWeight 3 k * (heatStokesMultiplier nu t k) ^ 2 =
        periodicSobolevWeight 2 k *
          (periodicSobolevWeight 1 k *
            (heatStokesMultiplier nu t k) ^ 2) := by
      simp only [periodicSobolevWeight, pow_one]
      ring
    _ ≤ periodicSobolevWeight 2 k * heatOneStepSquaredConstant nu t :=
      mul_le_mul_of_nonneg_left hone htwo
    _ = heatOneStepSquaredConstant nu t * periodicSobolevWeight 2 k := by ring

private theorem heat_order_three_weighted_term_eq
    (nu t : ℝ≥0) (coeff : PeriodicSobolevCoefficients 2)
    (k : SpatialFrequency) :
    periodicSobolevWeight 3 k *
        ‖infiniteHeatCoefficientEvolution nu t coeff.1 k‖ ^ 2 =
      (periodicSobolevWeight 3 k *
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) *
          ‖coeff.1 k‖ ^ 2 := by
  have hm0 : 0 ≤ heatStokesMultiplier (nu : ℝ) (t : ℝ) k :=
    (Real.exp_pos _).le
  simp only [infiniteHeatCoefficientEvolution_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  ring

/-- Every positive viscous time sends the honest complete H² carrier into H³. -/
theorem infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three_of_two
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicSobolevCoefficients 2) :
    HasPeriodicSobolevCoefficients 3
      (infiniteHeatCoefficientEvolution nu t coeff.1) := by
  let C := heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)
  have hsource : Summable fun k ↦
      C * (periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) :=
    coeff.2.mul_left C
  unfold HasPeriodicSobolevCoefficients
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg 3 k) (sq_nonneg _))
    (fun k ↦ ?_) hsource
  rw [heat_order_three_weighted_term_eq]
  have hmode := periodicSobolevWeight_three_mul_heat_sq_le_two hviscous k
  calc
    (periodicSobolevWeight 3 k *
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) *
        ‖coeff.1 k‖ ^ 2 ≤
      (C * periodicSobolevWeight 2 k) * ‖coeff.1 k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmode (sq_nonneg _)
    _ = C * (periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) := by ring

/-- The one-step heat return packaged in the complete order-three carrier. -/
def infiniteHeatPeriodicSobolevTwoIntoThree
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicSobolevCoefficients 2) :
    PeriodicSobolevCoefficients 3 :=
  ⟨infiniteHeatCoefficientEvolution nu t coeff.1,
    infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three_of_two
      nu t hviscous coeff⟩

@[simp]
theorem infiniteHeatPeriodicSobolevTwoIntoThree_apply
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicSobolevCoefficients 2) (k : SpatialFrequency) :
    (infiniteHeatPeriodicSobolevTwoIntoThree nu t hviscous coeff).1 k =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * coeff.1 k :=
  rfl

/-- Complete squared H²-to-H³ smoothing estimate with its exact positive-time singularity. -/
theorem periodicSobolevThreeSquaredEnergy_heatTwoIntoThree_le
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicSobolevCoefficients 2) :
    periodicSobolevThreeSquaredEnergy
        (infiniteHeatPeriodicSobolevTwoIntoThree nu t hviscous coeff) ≤
      heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
        (∑' k, periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) := by
  let C := heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)
  have hsmooth := infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three_of_two
    nu t hviscous coeff
  have hsource : Summable fun k ↦
      C * (periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) :=
    coeff.2.mul_left C
  have hpoint : ∀ k,
      periodicSobolevWeight 3 k *
          ‖infiniteHeatCoefficientEvolution nu t coeff.1 k‖ ^ 2 ≤
        C * (periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) := by
    intro k
    rw [heat_order_three_weighted_term_eq]
    have hmode := periodicSobolevWeight_three_mul_heat_sq_le_two hviscous k
    calc
      (periodicSobolevWeight 3 k *
          (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) *
          ‖coeff.1 k‖ ^ 2 ≤
        (C * periodicSobolevWeight 2 k) * ‖coeff.1 k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmode (sq_nonneg _)
      _ = C * (periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) := by ring
  unfold periodicSobolevThreeSquaredEnergy
  calc
    (∑' k, periodicSobolevWeight 3 k *
        ‖(infiniteHeatPeriodicSobolevTwoIntoThree nu t hviscous coeff).1 k‖ ^ 2) ≤
      ∑' k, C * (periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) :=
        hsmooth.tsum_le_tsum hpoint hsource
    _ = C * (∑' k, periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2) :=
      coeff.2.tsum_mul_left C

section Audit

#print axioms periodicSobolevWeight_three_mul_heat_sq_le_two
#print axioms infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three_of_two
#print axioms infiniteHeatPeriodicSobolevTwoIntoThree
#print axioms periodicSobolevThreeSquaredEnergy_heatTwoIntoThree_le

end Audit

end Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
