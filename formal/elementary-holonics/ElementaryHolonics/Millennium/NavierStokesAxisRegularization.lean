import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ElementaryHolonics.Millennium.NavierStokesAxialPrimitive

/-!
# Regularizing the axial integral quotient at the zero axis

The quotient of two primitives is represented at the base point by the quotient of their
`dslope`s.  This keeps the zero fibre explicit while agreeing with the ordinary ratio away from
the base point.  The first radial pressure coefficient is then given a continuous zero-axis
extension when its numerator source vanishes at the axis.
-/

noncomputable section

open ContDiff Set Filter MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesAxisRegularization

open Soma.Holonics.Millennium.NavierStokesAxialPrimitive

def intervalPrimitive (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..z, f t

theorem hasDerivAt_intervalPrimitive
    (f : ℝ → ℝ) (hf : Continuous f) (z : ℝ) :
    HasDerivAt (intervalPrimitive f) (f z) z := by
  unfold intervalPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 z)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter
    hf.continuousAt

def regularizedIntegralRatio (f g : ℝ → ℝ) (z : ℝ) : ℝ :=
  dslope (intervalPrimitive g) 0 z / dslope (intervalPrimitive f) 0 z

theorem intervalPrimitive_ne_zero_of_positive
    (f : ℝ → ℝ) (hf : Continuous f) (hpositive : ∀ z, 0 < f z)
    {z : ℝ} (hz : z ≠ 0) : intervalPrimitive f z ≠ 0 := by
  by_cases hzpos : 0 < z
  · exact (intervalIntegral.integral_pos hzpos (hf.continuousOn) (fun x _ ↦ (hpositive x).le)
      ⟨0, ⟨le_rfl, le_of_lt hzpos⟩, hpositive 0⟩).ne'
  · have hzneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
    rw [intervalPrimitive, intervalIntegral.integral_symm]
    apply neg_ne_zero.mpr
    exact (intervalIntegral.integral_pos hzneg (hf.continuousOn)
      (fun x _ ↦ (hpositive x).le)
      ⟨0, ⟨le_of_lt hzneg, le_rfl⟩, hpositive 0⟩).ne'

theorem regularizedIntegralRatio_eq_integralRatio_of_ne
    (f g : ℝ → ℝ) (hf : Continuous f) (hpositive : ∀ z, 0 < f z)
    {z : ℝ} (hz : z ≠ 0) :
    regularizedIntegralRatio f g z =
      intervalPrimitive g z / intervalPrimitive f z := by
  unfold regularizedIntegralRatio
  rw [dslope_of_ne _ hz, dslope_of_ne _ hz]
  unfold slope intervalPrimitive
  simp only [intervalIntegral.integral_same, vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp [intervalPrimitive_ne_zero_of_positive f hf hpositive hz]

theorem regularizedIntegralRatio_continuousAt_zero
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hpositive : ∀ z, 0 < f z) :
    ContinuousAt (regularizedIntegralRatio f g) 0 := by
  have hF : DifferentiableAt ℝ (intervalPrimitive f) 0 :=
    (hasDerivAt_intervalPrimitive f hf 0).differentiableAt
  have hG : DifferentiableAt ℝ (intervalPrimitive g) 0 :=
    (hasDerivAt_intervalPrimitive g hg 0).differentiableAt
  have hFcont : ContinuousAt (dslope (intervalPrimitive f) 0) 0 :=
    continuousAt_dslope_same.mpr hF
  have hGcont : ContinuousAt (dslope (intervalPrimitive g) 0) 0 :=
    continuousAt_dslope_same.mpr hG
  have hden : dslope (intervalPrimitive f) 0 0 ≠ 0 := by
    rw [dslope_same, (hasDerivAt_intervalPrimitive f hf 0).deriv]
    exact (hpositive 0).ne'
  exact hGcont.div hFcont hden

theorem regularizedIntegralRatio_zero_eq_ratio_of_derivatives
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    regularizedIntegralRatio f g 0 = g 0 / f 0 := by
  unfold regularizedIntegralRatio
  rw [dslope_same, dslope_same,
    (hasDerivAt_intervalPrimitive g hg 0).deriv,
    (hasDerivAt_intervalPrimitive f hf 0).deriv]

def axialHRegularized (k : ℝ) (A F : ℝ → ℝ) (z : ℝ) : ℝ :=
  (1 / (2 * k)) * regularizedIntegralRatio
    (fun t ↦ (F t)⁻¹) (fun t ↦ deriv A t / F t) z

theorem axialHRegularized_continuousAt_zero
    {k : ℝ} {A F : ℝ → ℝ}
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) :
    ContinuousAt (axialHRegularized k A F) 0 := by
  have hF' : Continuous (fun z ↦ (F z)⁻¹) :=
    hF.continuous.inv₀ (fun z ↦ (hpositive z).ne')
  have hAderiv : ContDiff ℝ 1 (deriv A) := hA.deriv' (n := 1)
  have hg : Continuous (fun z ↦ deriv A z / F z) :=
    (hAderiv.continuous.div hF.continuous (fun z ↦ (hpositive z).ne'))
  have hratio := regularizedIntegralRatio_continuousAt_zero
    (fun z ↦ (F z)⁻¹) (fun z ↦ deriv A z / F z) hF' hg
      (fun z ↦ inv_pos.mpr (hpositive z))
  exact (continuousAt_const.mul hratio)

theorem axialHRegularized_zero_eq_zero
    {k : ℝ} {A F : ℝ → ℝ}
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (hA0 : deriv A 0 = 0) :
    axialHRegularized k A F 0 = 0 := by
  have hF' : Continuous (fun z ↦ (F z)⁻¹) :=
    hF.continuous.inv₀ (fun z ↦ (hpositive z).ne')
  have hAderiv : ContDiff ℝ 1 (deriv A) := hA.deriv' (n := 1)
  have hg : Continuous (fun z ↦ deriv A z / F z) :=
    hAderiv.continuous.div hF.continuous (fun z ↦ (hpositive z).ne')
  unfold axialHRegularized
  rw [regularizedIntegralRatio_zero_eq_ratio_of_derivatives
    (fun z ↦ (F z)⁻¹) (fun z ↦ deriv A z / F z) hF' hg, hA0]
  simp

theorem axialH_eq_regularized
    (alpha beta : ℝ) (A F : ℝ → ℝ)
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (hk : alpha + 2 * beta ≠ 0)
    (hA0 : deriv A 0 = 0) (z : ℝ) :
    axialH alpha beta A F z =
      axialHRegularized (alpha + 2 * beta) A F z := by
  by_cases hz : z = 0
  · subst z
    rw [axialHRegularized_zero_eq_zero hA hF hpositive hA0]
    simp [axialH]
  · rw [axialH, if_neg hz, axialHRegularized,
      regularizedIntegralRatio_eq_integralRatio_of_ne
        (fun t ↦ (F t)⁻¹) (fun t ↦ deriv A t / F t)
        (hF.continuous.inv₀ (fun t ↦ (hpositive t).ne'))
        (fun t ↦ inv_pos.mpr (hpositive t)) hz]
    unfold intervalPrimitive axialJ axialGamma
    have hI : (∫ t in (0 : ℝ)..z, (F t)⁻¹) ≠ 0 :=
      intervalPrimitive_ne_zero_of_positive
        (fun t ↦ (F t)⁻¹)
        (hF.continuous.inv₀ (fun t ↦ (hpositive t).ne'))
        (fun t ↦ inv_pos.mpr (hpositive t)) hz
    simp only [div_eq_mul_inv]
    rw [show primitiveInv F z = ∫ t in (0 : ℝ)..z, (F t)⁻¹ by rfl]
    field_simp [hpositive z |>.ne', hk, hI]

theorem continuousAt_axialH_zero
    (alpha beta : ℝ) (A F : ℝ → ℝ)
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (hk : alpha + 2 * beta ≠ 0)
    (hA0 : deriv A 0 = 0) :
    ContinuousAt (axialH alpha beta A F) 0 := by
  have hfun : axialH alpha beta A F =
      axialHRegularized (alpha + 2 * beta) A F := by
    funext z
    exact axialH_eq_regularized alpha beta A F hA hF hpositive hk hA0 z
  rw [hfun]
  exact axialHRegularized_continuousAt_zero hA hF hpositive

section Audit

#print axioms hasDerivAt_intervalPrimitive
#print axioms regularizedIntegralRatio_eq_integralRatio_of_ne
#print axioms regularizedIntegralRatio_continuousAt_zero
#print axioms axialHRegularized_continuousAt_zero
#print axioms axialHRegularized_zero_eq_zero
#print axioms axialH_eq_regularized
#print axioms continuousAt_axialH_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesAxisRegularization
