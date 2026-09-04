import ElementaryHolonics.Millennium.NavierStokesWeightedHeatScale

/-!
# An ordered heat word crosses a finite Sobolev scale chain

**[proved-derived]** One adjacent positive-time heat passage may be composed without erasing its
intermediate Sobolev addresses.  A word of length `steps` begins at order `start`, visits every
successive scale, and returns at `start + steps`.  Its norm receipt is the corresponding power of
the one-step constant, while its unweighted coefficient is the repeated diagonal heat multiplier.

This is a finite linear smoothing word.  It neither asserts an infinite-order limit nor transports
the nonlinear Duhamel source.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedHeatScaleWord

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHeatScale
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Unweighting an adjacent-scale heat return exposes the same diagonal heat action on the
source's raw coefficient population. -/
theorem weightedSobolevCoefficients_periodicWeightedHeatSucc_apply
    (order : ℕ) (nu dt : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicWeightedSobolev order) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (order + 1)
      (periodicWeightedHeatSucc order nu dt hviscous state)).1 k =
        (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) *
          (weightedSobolevCoefficients order state).1 k := by
  let source := weightedSobolevCoefficients order state
  let target := infiniteHeatPeriodicSobolevSucc order nu dt hviscous source
  have hreconstruct := weightedSobolevCoefficients_coefficientWeightedRealization
    (order + 1) target
  have hmode := congrArg
    (fun coeff : PeriodicSobolevCoefficients (order + 1) ↦ coeff.1 k) hreconstruct
  exact hmode.trans (by rfl)

/-- The addressed serial word of `steps` adjacent positive-time heat passages. -/
def periodicWeightedHeatScaleWord
    (start : ℕ) : (steps : ℕ) → (nu dt : ℝ≥0) →
      0 < (nu : ℝ) * (dt : ℝ) →
      PeriodicWeightedSobolev start →L[ℂ]
        PeriodicWeightedSobolev (start + steps)
  | 0, _nu, _dt, _hviscous => ContinuousLinearMap.id ℂ _
  | steps + 1, nu, dt, hviscous =>
      (periodicWeightedHeatSuccCLM (start + steps) nu dt hviscous).comp
        (periodicWeightedHeatScaleWord start steps nu dt hviscous)

@[simp]
theorem periodicWeightedHeatScaleWord_zero
    (start : ℕ) (nu dt : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (dt : ℝ)) :
    periodicWeightedHeatScaleWord start 0 nu dt hviscous =
      ContinuousLinearMap.id ℂ _ :=
  rfl

@[simp]
theorem periodicWeightedHeatScaleWord_succ
    (start steps : ℕ) (nu dt : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (dt : ℝ)) :
    periodicWeightedHeatScaleWord start (steps + 1) nu dt hviscous =
      (periodicWeightedHeatSuccCLM (start + steps) nu dt hviscous).comp
        (periodicWeightedHeatScaleWord start steps nu dt hviscous) :=
  rfl

/-- Every intermediate reweighting cancels under the raw coefficient receiver, leaving the
ordered product of exactly `steps` identical heat multipliers. -/
theorem weightedSobolevCoefficients_periodicWeightedHeatScaleWord_apply
    (start steps : ℕ) (nu dt : ℝ≥0)
    (hviscous : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicWeightedSobolev start) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (start + steps)
      (periodicWeightedHeatScaleWord start steps nu dt hviscous state)).1 k =
        (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) ^ steps *
          (weightedSobolevCoefficients start state).1 k := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      rw [periodicWeightedHeatScaleWord_succ]
      change
        (weightedSobolevCoefficients ((start + steps) + 1)
          (periodicWeightedHeatSucc (start + steps) nu dt hviscous
            (periodicWeightedHeatScaleWord start steps nu dt hviscous state))).1 k = _
      rw [weightedSobolevCoefficients_periodicWeightedHeatSucc_apply, ih]
      simp only [pow_succ]
      ring

/-- The complete norm receipt of the finite ordered scale word. -/
theorem norm_periodicWeightedHeatScaleWord_le
    (start steps : ℕ) (nu dt : ℝ≥0)
    (hviscous : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicWeightedSobolev start) :
    ‖periodicWeightedHeatScaleWord start steps nu dt hviscous state‖ ≤
      (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps * ‖state‖ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [periodicWeightedHeatScaleWord_succ]
      change ‖periodicWeightedHeatSucc (start + steps) nu dt hviscous
          (periodicWeightedHeatScaleWord start steps nu dt hviscous state)‖ ≤ _
      calc
        _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ)) *
            ‖periodicWeightedHeatScaleWord start steps nu dt hviscous state‖ :=
          norm_periodicWeightedHeatSucc_le (start + steps) nu dt hviscous _
        _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ)) *
            ((Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps *
              ‖state‖) :=
          mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _)
        _ = (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ (steps + 1) *
            ‖state‖ := by
          rw [pow_succ]
          ring

/-! ## The complete three-component word -/

/-- Apply the same addressed scale word to all three velocity components without collapsing their
mode or component lineage. -/
def periodicVectorWeightedHeatScaleWord
    (start steps : ℕ) (nu dt : ℝ≥0)
    (hviscous : 0 < (nu : ℝ) * (dt : ℝ)) :
    PeriodicVectorWeightedSobolev start →L[ℂ]
      PeriodicVectorWeightedSobolev (start + steps) :=
  LinearMap.mkContinuous
    { toFun := fun state component ↦
        periodicWeightedHeatScaleWord start steps nu dt hviscous (state component)
      map_add' := by
        intro left right
        funext component
        exact (periodicWeightedHeatScaleWord start steps nu dt hviscous).map_add
          (left component) (right component)
      map_smul' := by
        intro scalar state
        funext component
        exact (periodicWeightedHeatScaleWord start steps nu dt hviscous).map_smul
          scalar (state component) }
    ((Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps)
    (fun state ↦ by
      have hconstant : 0 ≤
          (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps * ‖state‖ :=
        mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)
      rw [pi_norm_le_iff_of_nonneg hconstant]
      intro component
      calc
        ‖periodicWeightedHeatScaleWord start steps nu dt hviscous (state component)‖ ≤
            (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps *
              ‖state component‖ :=
          norm_periodicWeightedHeatScaleWord_le start steps nu dt hviscous _
        _ ≤ (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps *
              ‖state‖ :=
          mul_le_mul_of_nonneg_left (norm_le_pi_norm state component)
            (pow_nonneg (Real.sqrt_nonneg _) _))

/-- Every addressed component and frequency sees exactly the same repeated diagonal heat word. -/
theorem weightedSobolevCoefficients_periodicVectorWeightedHeatScaleWord_apply
    (start steps : ℕ) (nu dt : ℝ≥0)
    (hviscous : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev start)
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (start + steps)
      (periodicVectorWeightedHeatScaleWord start steps nu dt hviscous state component)).1 k =
        (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) ^ steps *
          (weightedSobolevCoefficients start (state component)).1 k :=
  weightedSobolevCoefficients_periodicWeightedHeatScaleWord_apply
    start steps nu dt hviscous (state component) k

section Audit

#print axioms weightedSobolevCoefficients_periodicWeightedHeatSucc_apply
#print axioms periodicWeightedHeatScaleWord
#print axioms weightedSobolevCoefficients_periodicWeightedHeatScaleWord_apply
#print axioms norm_periodicWeightedHeatScaleWord_le
#print axioms periodicVectorWeightedHeatScaleWord
#print axioms weightedSobolevCoefficients_periodicVectorWeightedHeatScaleWord_apply

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHeatScaleWord
