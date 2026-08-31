import ElementaryHolonics.Millennium.NavierStokesWeightedHeatSemigroup
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integrable Duhamel heat-kernel singularity

The one-derivative weighted heat passage has norm constant
`sqrt (1 + (2 * ν * τ)⁻¹)`.  Its positive-time singularity is only of order
`τ⁻¹⁄²`, hence it is integrable at the Duhamel endpoint.  This owner records that
real-analysis fact and an explicit finite interval-integral bound.

Lean's inverse is total and sends zero to zero, so the displayed kernel takes the harmless
representative value `1` at `τ = 0`.  Changing that single endpoint value does not change either
interval integrability or the interval integral.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral

open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing

/-- The totalized real representative of the positive-time H²-to-H³ heat norm constant. -/
def duhamelHeatKernelMajorant (nu tau : ℝ) : ℝ :=
  Real.sqrt (heatOneStepSquaredConstant nu tau)

/-- The elementary square-root subadditivity estimate used at the Duhamel endpoint. -/
theorem sqrt_one_add_le_one_add_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]

/-- The heat norm constant is bounded by an explicitly integrable inverse-square-root kernel. -/
theorem duhamelHeatKernelMajorant_le_inverseSqrt
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 ≤ tau) :
    duhamelHeatKernelMajorant nu tau ≤
      1 + (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)) := by
  have htwoNu : 0 ≤ 2 * nu := by positivity
  have hproduct : 0 ≤ (2 * nu) * tau := mul_nonneg htwoNu htau
  have hinverse : 0 ≤ ((2 * nu) * tau)⁻¹ := inv_nonneg.mpr hproduct
  have hsqrtInverse :
      Real.sqrt (((2 * nu) * tau)⁻¹) =
        (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)) := by
    calc
      Real.sqrt (((2 * nu) * tau)⁻¹) =
          (Real.sqrt ((2 * nu) * tau))⁻¹ := Real.sqrt_inv _
      _ = (Real.sqrt (2 * nu) * Real.sqrt tau)⁻¹ := by
        rw [Real.sqrt_mul htwoNu]
      _ = (Real.sqrt (2 * nu))⁻¹ * (Real.sqrt tau)⁻¹ := by
        rw [mul_inv_rev]
        ring
      _ = (Real.sqrt (2 * nu))⁻¹ * (tau ^ (1 / 2 : ℝ))⁻¹ := by
        congr 1
        exact congrArg Inv.inv (Real.sqrt_eq_rpow tau)
      _ = (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg htau]
  unfold duhamelHeatKernelMajorant heatOneStepSquaredConstant
  rw [show 2 * (nu * tau) = (2 * nu) * tau by ring]
  calc
    Real.sqrt (1 + ((2 * nu) * tau)⁻¹) ≤
        1 + Real.sqrt (((2 * nu) * tau)⁻¹) :=
      sqrt_one_add_le_one_add_sqrt hinverse
    _ = 1 + (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)) := by
      rw [hsqrtInverse]

/-- The singular H²-to-H³ heat norm constant is interval-integrable through `τ = 0`. -/
theorem intervalIntegrable_duhamelHeatKernelMajorant
    {nu T : ℝ} (hnu : 0 < nu) (hT : 0 < T) :
    IntervalIntegrable (duhamelHeatKernelMajorant nu) volume 0 T := by
  have hrpow : IntervalIntegrable (fun tau : ℝ ↦ tau ^ (-(1 / 2 : ℝ))) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hbound : IntervalIntegrable
      (fun tau : ℝ ↦ 1 + (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)))
      volume 0 T :=
    intervalIntegrable_const.add
      (hrpow.const_mul (Real.sqrt (2 * nu))⁻¹)
  apply hbound.mono_fun'
  · unfold duhamelHeatKernelMajorant heatOneStepSquaredConstant
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.mul measurable_id)).inv)).sqrt.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with tau htau
    rw [uIoc_of_le hT.le] at htau
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ duhamelHeatKernelMajorant nu tau by
      exact Real.sqrt_nonneg _)]
    exact duhamelHeatKernelMajorant_le_inverseSqrt hnu htau.1.le

/-- The exact primitive of the endpoint model `τ⁻¹⁄²` on a nonnegative interval. -/
theorem intervalIntegral_rpow_neg_half
    {T : ℝ} (_hT : 0 ≤ T) :
    (∫ tau in (0 : ℝ)..T, tau ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt T := by
  rw [integral_rpow (a := 0) (b := T) (r := -(1 / 2 : ℝ))
    (Or.inl (by norm_num))]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring]
  rw [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
  rw [← Real.sqrt_eq_rpow]
  ring

/-- Explicit finite Duhamel-kernel budget on `[0, T]`. -/
theorem intervalIntegral_duhamelHeatKernelMajorant_le
    {nu T : ℝ} (hnu : 0 < nu) (hT : 0 < T) :
    (∫ tau in (0 : ℝ)..T, duhamelHeatKernelMajorant nu tau) ≤
      T + 2 * Real.sqrt (T / (2 * nu)) := by
  have hkernel := intervalIntegrable_duhamelHeatKernelMajorant hnu hT
  have hrpow : IntervalIntegrable (fun tau : ℝ ↦ tau ^ (-(1 / 2 : ℝ))) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hone : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 T :=
    intervalIntegrable_const
  have hscaled : IntervalIntegrable
      (fun tau : ℝ ↦ (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)))
      volume 0 T :=
    hrpow.const_mul (Real.sqrt (2 * nu))⁻¹
  have hbound : IntervalIntegrable
      (fun tau : ℝ ↦ 1 + (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)))
      volume 0 T :=
    hone.add hscaled
  calc
    (∫ tau in (0 : ℝ)..T, duhamelHeatKernelMajorant nu tau) ≤
        ∫ tau in (0 : ℝ)..T,
          1 + (Real.sqrt (2 * nu))⁻¹ * tau ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hT.le hkernel hbound
        (fun tau htau ↦ duhamelHeatKernelMajorant_le_inverseSqrt hnu htau.1.le)
    _ = T + 2 * Real.sqrt (T / (2 * nu)) := by
      rw [intervalIntegral.integral_add hone hscaled]
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral_rpow_neg_half hT.le]
      rw [Real.sqrt_div hT.le]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, div_eq_mul_inv]
      ring

section Audit

#print axioms sqrt_one_add_le_one_add_sqrt
#print axioms duhamelHeatKernelMajorant_le_inverseSqrt
#print axioms intervalIntegrable_duhamelHeatKernelMajorant
#print axioms intervalIntegral_rpow_neg_half
#print axioms intervalIntegral_duhamelHeatKernelMajorant_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
