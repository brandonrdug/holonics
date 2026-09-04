import ElementaryHolonics.Millennium.NavierStokesWeightedHeatSemigroup

/-!
# One viscous passage crosses every adjacent weighted Sobolev scale

**[proved-derived]** The existing native heat owner packages the one step `H² → H³` needed by
the local fixed point.  Its multiplier estimate is not special to those two indices.  This owner
retains the Sobolev address and proves the same exact passage from order `n` to order `n + 1` for
every natural `n`, with the unchanged positive-time constant

`1 + (2 ν t)⁻¹`.

The result is linear heat smoothing only.  It does not assert that the nonlinear mild path has
higher regularity; that later return must transport its Duhamel source through the same scale.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedHeatScale

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The scale-uniform multiplier law -/

/-- The adjacent target weight factors as the source weight times the single derivative weight,
so the existing one-step heat estimate applies at every addressed Sobolev scale. -/
theorem periodicSobolevWeight_succ_mul_heat_sq_le
    (order : ℕ) {nu t : ℝ} (hviscous : 0 < nu * t) (k : SpatialFrequency) :
    periodicSobolevWeight (order + 1) k * (heatStokesMultiplier nu t k) ^ 2 ≤
      heatOneStepSquaredConstant nu t * periodicSobolevWeight order k := by
  have hone := periodicSobolevWeight_one_mul_heat_sq_le hviscous k
  have horder : 0 ≤ periodicSobolevWeight order k :=
    periodicSobolevWeight_nonneg order k
  calc
    periodicSobolevWeight (order + 1) k * (heatStokesMultiplier nu t k) ^ 2 =
        periodicSobolevWeight order k *
          (periodicSobolevWeight 1 k * (heatStokesMultiplier nu t k) ^ 2) := by
      simp only [periodicSobolevWeight, pow_succ]
      ring
    _ ≤ periodicSobolevWeight order k * heatOneStepSquaredConstant nu t :=
      mul_le_mul_of_nonneg_left hone horder
    _ = heatOneStepSquaredConstant nu t * periodicSobolevWeight order k := by ring

private theorem heat_succ_weighted_term_eq
    (order : ℕ) (nu t : ℝ≥0) (coeff : PeriodicSobolevCoefficients order)
    (k : SpatialFrequency) :
    periodicSobolevWeight (order + 1) k *
        ‖infiniteHeatCoefficientEvolution nu t coeff.1 k‖ ^ 2 =
      (periodicSobolevWeight (order + 1) k *
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) * ‖coeff.1 k‖ ^ 2 := by
  have hm0 : 0 ≤ heatStokesMultiplier (nu : ℝ) (t : ℝ) k :=
    (Real.exp_pos _).le
  simp only [infiniteHeatCoefficientEvolution_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  ring

/-- Every positive viscous time sends the complete order-`n` coefficient carrier into the
complete order-`n+1` carrier. -/
theorem infiniteHeatCoefficientEvolution_hasPeriodicSobolev_succ
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicSobolevCoefficients order) :
    HasPeriodicSobolevCoefficients (order + 1)
      (infiniteHeatCoefficientEvolution nu t coeff.1) := by
  let C := heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)
  have hsource : Summable fun k ↦
      C * (periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2) :=
    coeff.2.mul_left C
  unfold HasPeriodicSobolevCoefficients
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg (order + 1) k) (sq_nonneg _))
    (fun k ↦ ?_) hsource
  rw [heat_succ_weighted_term_eq]
  have hmode := periodicSobolevWeight_succ_mul_heat_sq_le order hviscous k
  calc
    (periodicSobolevWeight (order + 1) k *
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) * ‖coeff.1 k‖ ^ 2 ≤
      (C * periodicSobolevWeight order k) * ‖coeff.1 k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmode (sq_nonneg _)
    _ = C * (periodicSobolevWeight order k * ‖coeff.1 k‖ ^ 2) := by ring

/-- The arbitrary adjacent-scale heat return in the older coefficient carrier. -/
def infiniteHeatPeriodicSobolevSucc
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicSobolevCoefficients order) :
    PeriodicSobolevCoefficients (order + 1) :=
  ⟨infiniteHeatCoefficientEvolution nu t coeff.1,
    infiniteHeatCoefficientEvolution_hasPeriodicSobolev_succ
      order nu t hviscous coeff⟩

@[simp]
theorem infiniteHeatPeriodicSobolevSucc_apply
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicSobolevCoefficients order) (k : SpatialFrequency) :
    (infiniteHeatPeriodicSobolevSucc order nu t hviscous coeff).1 k =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * coeff.1 k :=
  rfl

/-! ## Native complete Hilbert transport -/

/-- Unweight at the source scale, cross one positive-time heat passage, and reweight at the
adjacent target scale. -/
def periodicWeightedHeatSucc
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev order) :
    PeriodicWeightedSobolev (order + 1) :=
  coefficientWeightedRealization (order + 1)
    (infiniteHeatPeriodicSobolevSucc order nu t hviscous
      (weightedSobolevCoefficients order state))

@[simp]
theorem periodicWeightedHeatSucc_apply
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev order) (k : SpatialFrequency) :
    periodicWeightedHeatSucc order nu t hviscous state k =
      (Real.sqrt (periodicSobolevWeight (order + 1) k) : ℂ) *
        ((heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
          ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k)) :=
  rfl

/-- Exact squared native norm estimate for one arbitrary recovered derivative. -/
theorem norm_periodicWeightedHeatSucc_sq_le
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev order) :
    ‖periodicWeightedHeatSucc order nu t hviscous state‖ ^ 2 ≤
      heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 := by
  let source := weightedSobolevCoefficients order state
  let target := infiniteHeatPeriodicSobolevSucc order nu t hviscous source
  rw [show periodicWeightedHeatSucc order nu t hviscous state =
      coefficientWeightedRealization (order + 1) target by rfl]
  rw [norm_coefficientWeightedRealization_sq_eq]
  have htarget : Summable fun k ↦
      periodicSobolevWeight (order + 1) k * ‖target.1 k‖ ^ 2 := target.2
  have hsource : Summable fun k ↦
      heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
        (periodicSobolevWeight order k * ‖source.1 k‖ ^ 2) :=
    source.2.mul_left _
  have hpoint : ∀ k,
      periodicSobolevWeight (order + 1) k * ‖target.1 k‖ ^ 2 ≤
        heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
          (periodicSobolevWeight order k * ‖source.1 k‖ ^ 2) := by
    intro k
    rw [show target.1 k = infiniteHeatCoefficientEvolution nu t source.1 k by rfl,
      heat_succ_weighted_term_eq]
    have hmode := periodicSobolevWeight_succ_mul_heat_sq_le order hviscous k
    exact (mul_le_mul_of_nonneg_right hmode (sq_nonneg _)).trans_eq (by ring)
  calc
    (∑' k, periodicSobolevWeight (order + 1) k * ‖target.1 k‖ ^ 2) ≤
        ∑' k, heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
          (periodicSobolevWeight order k * ‖source.1 k‖ ^ 2) :=
      htarget.tsum_le_tsum hpoint hsource
    _ = heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
        (∑' k, periodicSobolevWeight order k * ‖source.1 k‖ ^ 2) :=
      source.2.tsum_mul_left _
    _ = heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
        ‖coefficientWeightedRealization order source‖ ^ 2 := by
      rw [norm_coefficientWeightedRealization_sq_eq]
    _ = heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 := by
      rw [coefficientWeightedRealization_weightedSobolevCoefficients]

/-- Unsquared operator estimate at every adjacent scale. -/
theorem norm_periodicWeightedHeatSucc_le
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev order) :
    ‖periodicWeightedHeatSucc order nu t hviscous state‖ ≤
      Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖ := by
  have hsquare := norm_periodicWeightedHeatSucc_sq_le order nu t hviscous state
  have hC := heatOneStepSquaredConstant_nonneg hviscous
  have hsqrt := Real.sq_sqrt hC
  have htargetSquare :
      (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖) ^ 2 =
        heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 := by
    rw [mul_pow, hsqrt]
  let outputNorm := ‖periodicWeightedHeatSucc order nu t hviscous state‖
  let targetNorm :=
    Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖
  have houtputNonneg : 0 ≤ outputNorm := norm_nonneg _
  have htargetNonneg : 0 ≤ targetNorm :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  by_contra hle
  have hlt : targetNorm < outputNorm := lt_of_not_ge hle
  have hdiff : 0 < outputNorm - targetNorm := sub_pos.mpr hlt
  have hsum : 0 < outputNorm + targetNorm := by nlinarith
  have hsq : targetNorm ^ 2 < outputNorm ^ 2 := by
    nlinarith [mul_pos hdiff hsum]
  change outputNorm ^ 2 ≤
    heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 at hsquare
  change targetNorm ^ 2 =
    heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 at htargetSquare
  nlinarith

/-- Adjacent-scale heat smoothing as a genuine continuous linear map. -/
def periodicWeightedHeatSuccCLM
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ)) :
    PeriodicWeightedSobolev order →L[ℂ] PeriodicWeightedSobolev (order + 1) :=
  LinearMap.mkContinuous
    { toFun := periodicWeightedHeatSucc order nu t hviscous
      map_add' := by
        intro left right
        apply Subtype.ext
        funext k
        simp only [periodicWeightedHeatSucc_apply, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        funext k
        simp only [periodicWeightedHeatSucc_apply, lp.coeFn_smul, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        ring }
    (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)))
    (norm_periodicWeightedHeatSucc_le order nu t hviscous)

/-- Componentwise adjacent-scale smoothing on the complete three-component carrier. -/
def periodicVectorWeightedHeatSuccCLM
    (order : ℕ) (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ)) :
    PeriodicVectorWeightedSobolev order →L[ℂ]
      PeriodicVectorWeightedSobolev (order + 1) :=
  LinearMap.mkContinuous
    { toFun := fun state component ↦
        periodicWeightedHeatSucc order nu t hviscous (state component)
      map_add' := by
        intro left right
        funext component
        exact (periodicWeightedHeatSuccCLM order nu t hviscous).map_add
          (left component) (right component)
      map_smul' := by
        intro scalar state
        funext component
        exact (periodicWeightedHeatSuccCLM order nu t hviscous).map_smul
          scalar (state component) }
    (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)))
    (fun state ↦ by
      have hconstant : 0 ≤
          Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      rw [pi_norm_le_iff_of_nonneg hconstant]
      intro component
      calc
        ‖periodicWeightedHeatSucc order nu t hviscous (state component)‖ ≤
            Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) *
              ‖state component‖ :=
          norm_periodicWeightedHeatSucc_le order nu t hviscous (state component)
        _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖ :=
          mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) (Real.sqrt_nonneg _))

section Audit

#print axioms periodicSobolevWeight_succ_mul_heat_sq_le
#print axioms infiniteHeatCoefficientEvolution_hasPeriodicSobolev_succ
#print axioms periodicWeightedHeatSucc
#print axioms norm_periodicWeightedHeatSucc_le
#print axioms periodicWeightedHeatSuccCLM
#print axioms periodicVectorWeightedHeatSuccCLM

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHeatScale
