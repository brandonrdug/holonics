import ElementaryHolonics.Millennium.NavierStokesWeightedSobolevHilbert

/-!
# Heat transport on the complete weighted Sobolev realization

The native weighted carrier is an ordinary ℓ2 Hilbert space.  Since the diagonal heat multiplier
commutes with every fixed Sobolev weight, it acts contractively at each order.  Between orders two
and three the same multiplier recovers one derivative with operator bound

`sqrt (1 + (2 ν t)⁻¹)`.

This file packages both passages as genuine continuous linear maps, including the three-component
vector carrier.  These are the semigroup ports required by a later Bochner--Duhamel contraction.
-/

noncomputable section

open Filter Topology
open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup

open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Contractive same-order transport -/

/-- Heat transport as a continuous linear contraction on any native weighted Sobolev order. -/
def periodicWeightedHeat
    (order : ℕ) (nu t : ℝ≥0) :
    PeriodicWeightedSobolev order →L[ℂ] PeriodicWeightedSobolev order :=
  LinearMap.mkContinuous
    { toFun := fun state ↦ infiniteHeatCoefficientEvolution nu t state
      map_add' := by
        intro left right
        apply Subtype.ext
        funext k
        simp only [infiniteHeatCoefficientEvolution_apply, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        funext k
        simp only [infiniteHeatCoefficientEvolution_apply, lp.coeFn_smul, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        ring }
    1 (fun state ↦ by
      simpa using norm_infiniteHeatCoefficientEvolution_le nu t state)

@[simp]
theorem periodicWeightedHeat_apply
    (order : ℕ) (nu t : ℝ≥0) (state : PeriodicWeightedSobolev order)
    (k : SpatialFrequency) :
    periodicWeightedHeat order nu t state k =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * state k :=
  rfl

theorem norm_periodicWeightedHeat_le
    (order : ℕ) (nu t : ℝ≥0) (state : PeriodicWeightedSobolev order) :
    ‖periodicWeightedHeat order nu t state‖ ≤ ‖state‖ :=
  norm_infiniteHeatCoefficientEvolution_le nu t state

@[simp]
theorem periodicWeightedHeat_zero_time
    (order : ℕ) (nu : ℝ≥0) :
    periodicWeightedHeat order nu 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro state
  exact infiniteHeatCoefficientEvolution_zero_time nu state

theorem periodicWeightedHeat_add
    (order : ℕ) (nu s t : ℝ≥0) :
    periodicWeightedHeat order nu (s + t) =
      (periodicWeightedHeat order nu s).comp (periodicWeightedHeat order nu t) := by
  apply ContinuousLinearMap.ext
  intro state
  exact infiniteHeatCoefficientEvolution_add nu s t state

/-- Strong continuity at zero in every native weighted Sobolev norm. -/
theorem tendsto_periodicWeightedHeat_zero_time
    (order : ℕ) (nu : ℝ≥0) (state : PeriodicWeightedSobolev order) :
    Tendsto (fun t : ℝ≥0 ↦ periodicWeightedHeat order nu t state)
      (𝓝 0) (𝓝 state) :=
  tendsto_infiniteHeatCoefficientEvolution_zero_time nu state

/-! ## One recovered derivative -/

/-- The native order-two to order-three heat passage. -/
def periodicWeightedHeatTwoToThree
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev 2) : PeriodicWeightedSobolev 3 :=
  coefficientWeightedRealization 3
    (infiniteHeatPeriodicSobolevTwoIntoThree nu t hviscous
      (weightedSobolevCoefficients 2 state))

@[simp]
theorem periodicWeightedHeatTwoToThree_apply
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev 2) (k : SpatialFrequency) :
    periodicWeightedHeatTwoToThree nu t hviscous state k =
      (Real.sqrt (periodicSobolevWeight 3 k) : ℂ) *
        ((heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
          ((((Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ) * state k)) :=
  rfl

/-- Squared native norm estimate for one recovered derivative. -/
theorem norm_periodicWeightedHeatTwoToThree_sq_le
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev 2) :
    ‖periodicWeightedHeatTwoToThree nu t hviscous state‖ ^ 2 ≤
      heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 := by
  let source := weightedSobolevCoefficients 2 state
  let target := infiniteHeatPeriodicSobolevTwoIntoThree nu t hviscous source
  have htarget := norm_coefficientWeightedRealization_sq_eq 3 target
  have hsmooth := periodicSobolevThreeSquaredEnergy_heatTwoIntoThree_le
    nu t hviscous source
  have hsource := norm_coefficientWeightedRealization_sq_eq 2 source
  have hreconstruct : coefficientWeightedRealization 2 source = state :=
    coefficientWeightedRealization_weightedSobolevCoefficients 2 state
  change ‖coefficientWeightedRealization 3 target‖ ^ 2 ≤
    heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2
  rw [htarget]
  calc
    (∑' k, periodicSobolevWeight 3 k * ‖target.1 k‖ ^ 2) ≤
        heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
          (∑' k, periodicSobolevWeight 2 k * ‖source.1 k‖ ^ 2) := hsmooth
    _ = heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) *
        ‖coefficientWeightedRealization 2 source‖ ^ 2 := by rw [hsource]
    _ = heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 := by
      rw [hreconstruct]

/-- Operator norm estimate in unsquared form. -/
theorem norm_periodicWeightedHeatTwoToThree_le
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev 2) :
    ‖periodicWeightedHeatTwoToThree nu t hviscous state‖ ≤
      Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖ := by
  have hsquare := norm_periodicWeightedHeatTwoToThree_sq_le nu t hviscous state
  have hC := heatOneStepSquaredConstant_nonneg hviscous
  have hsqrt := Real.sq_sqrt hC
  have htargetSquare :
      (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖) ^ 2 =
        heatOneStepSquaredConstant (nu : ℝ) (t : ℝ) * ‖state‖ ^ 2 := by
    rw [mul_pow, hsqrt]
  let outputNorm := ‖periodicWeightedHeatTwoToThree nu t hviscous state‖
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

/-- The one-derivative passage as a genuine continuous linear map. -/
def periodicWeightedHeatTwoToThreeCLM
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ)) :
    PeriodicWeightedSobolev 2 →L[ℂ] PeriodicWeightedSobolev 3 :=
  LinearMap.mkContinuous
    { toFun := periodicWeightedHeatTwoToThree nu t hviscous
      map_add' := by
        intro left right
        apply Subtype.ext
        funext k
        simp only [periodicWeightedHeatTwoToThree_apply, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        funext k
        simp only [periodicWeightedHeatTwoToThree_apply, lp.coeFn_smul, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        ring }
    (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)))
    (norm_periodicWeightedHeatTwoToThree_le nu t hviscous)

/-! ## Three-component assembly -/

/-- Componentwise heat contraction on the complete vector weighted carrier. -/
def periodicVectorWeightedHeat
    (order : ℕ) (nu t : ℝ≥0) :
    PeriodicVectorWeightedSobolev order →L[ℂ]
      PeriodicVectorWeightedSobolev order :=
  LinearMap.mkContinuous
    { toFun := fun state component ↦ periodicWeightedHeat order nu t (state component)
      map_add' := by
        intro left right
        funext component
        exact (periodicWeightedHeat order nu t).map_add
          (left component) (right component)
      map_smul' := by
        intro scalar state
        funext component
        exact (periodicWeightedHeat order nu t).map_smul scalar (state component) }
    1 (fun state ↦ by
      rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 * ‖state‖)]
      intro component
      calc
        ‖periodicWeightedHeat order nu t (state component)‖ ≤ ‖state component‖ :=
          norm_periodicWeightedHeat_le order nu t (state component)
        _ ≤ ‖state‖ := norm_le_pi_norm state component
        _ = 1 * ‖state‖ := by ring)

/-- Componentwise one-derivative heat smoothing on the vector carrier. -/
def periodicVectorWeightedHeatTwoToThree
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ)) :
    PeriodicVectorWeightedSobolev 2 →L[ℂ]
      PeriodicVectorWeightedSobolev 3 :=
  LinearMap.mkContinuous
    { toFun := fun state component ↦
        periodicWeightedHeatTwoToThree nu t hviscous (state component)
      map_add' := by
        intro left right
        funext component
        exact (periodicWeightedHeatTwoToThreeCLM nu t hviscous).map_add
          (left component) (right component)
      map_smul' := by
        intro scalar state
        funext component
        exact (periodicWeightedHeatTwoToThreeCLM nu t hviscous).map_smul
          scalar (state component) }
    (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)))
    (fun state ↦ by
      have hconstant : 0 ≤
          Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) * ‖state‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      rw [pi_norm_le_iff_of_nonneg hconstant]
      intro component
      calc
        ‖periodicWeightedHeatTwoToThree nu t hviscous (state component)‖ ≤
            Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) *
              ‖state component‖ :=
          norm_periodicWeightedHeatTwoToThree_le nu t hviscous (state component)
        _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t : ℝ)) *
              ‖state‖ :=
          mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) (Real.sqrt_nonneg _))

section Audit

#print axioms periodicWeightedHeat
#print axioms tendsto_periodicWeightedHeat_zero_time
#print axioms norm_periodicWeightedHeatTwoToThree_le
#print axioms periodicWeightedHeatTwoToThreeCLM
#print axioms periodicVectorWeightedHeatTwoToThree

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
