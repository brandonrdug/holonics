import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Axial primitives

This owner records the exact primitive construction behind the axial scalar ODE.  The returned
identities are obtained by differentiating the displayed interval integrals; no target ODE is
introduced as an assumption.
-/

noncomputable section

open ContDiff Set MeasureTheory Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesAxialPrimitive

/-- The reciprocal primitive based at the axial origin. -/
def primitiveInv (F : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..z, (F t)⁻¹

/-- The accumulated axial factor, with `k = α + 2β`. -/
def axialGamma (alpha beta : ℝ) (F : ℝ → ℝ) (z : ℝ) : ℝ :=
  (alpha + 2 * beta) * F z * primitiveInv F z

/-- The axial velocity, with coordinate dilation removed from `Gamma`. -/
def axialW (alpha beta : ℝ) (F : ℝ → ℝ) (z : ℝ) : ℝ :=
  axialGamma alpha beta F z - beta * z

/-- The primitive derivative is the reciprocal source value. -/
theorem hasDerivAt_primitiveInv
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z) (z : ℝ) :
    HasDerivAt (primitiveInv F) ((F z)⁻¹) z := by
  have hcontinuous : Continuous fun t : ℝ => (F t)⁻¹ := by
    exact hF.continuous.inv₀ (fun t => (hpositive t).ne')
  change HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, (F t)⁻¹) ((F z)⁻¹) z
  exact intervalIntegral.integral_hasDerivAt_right
      (hcontinuous.intervalIntegrable (0 : ℝ) z)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcontinuous.continuousAt

theorem contDiff_infty_primitiveInv (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z, 0 < F z) : ContDiff ℝ ∞ (primitiveInv F) := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun z ↦ (hasDerivAt_primitiveInv F hF2 hpositive z).differentiableAt, ?_⟩
  have heq : deriv (primitiveInv F) = fun z ↦ (F z)⁻¹ :=
    funext fun z ↦ (hasDerivAt_primitiveInv F hF2 hpositive z).deriv
  rw [heq]
  have hquot : ContDiff ℝ ∞ (fun z ↦ (1 : ℝ) / F z) :=
    contDiff_const.div hF (fun z ↦ (hpositive z).ne')
  have hsame : (fun z ↦ (1 : ℝ) / F z) = (fun z ↦ (F z)⁻¹) := by
    funext z
    exact one_div _
  rw [← hsame]
  exact hquot

theorem contDiff_infty_axialW (alpha beta : ℝ) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z, 0 < F z) : ContDiff ℝ ∞ (axialW alpha beta F) := by
  have hI := contDiff_infty_primitiveInv F hF hpositive
  unfold axialW axialGamma
  fun_prop

@[simp] theorem primitiveInv_zero (F : ℝ → ℝ) : primitiveInv F 0 = 0 := by
  simp [primitiveInv]

@[simp] theorem axialW_zero (alpha beta : ℝ) (F : ℝ → ℝ) : axialW alpha beta F 0 = 0 := by
  simp [axialW, axialGamma]

/-- The reciprocal primitive is strictly positive to the right of the axis. -/
theorem primitiveInv_pos_of_pos
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    {z : ℝ} (hz : 0 < z) :
    0 < primitiveInv F z := by
  have hcontinuous : Continuous fun t : ℝ => (F t)⁻¹ :=
    hF.continuous.inv₀ (fun t => (hpositive t).ne')
  exact intervalIntegral.intervalIntegral_pos_of_pos
    (hcontinuous.intervalIntegrable (0 : ℝ) z)
      (fun x => inv_pos.mpr (hpositive x)) hz

/-- The reciprocal primitive is nonzero away from the axial origin. -/
theorem primitiveInv_ne_zero_of_ne_zero
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    {z : ℝ} (hz : z ≠ 0) :
    primitiveInv F z ≠ 0 := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hcontinuous : Continuous fun t : ℝ => (F t)⁻¹ :=
      hF.continuous.inv₀ (fun t => (hpositive t).ne')
    have hpos : 0 < ∫ t in z..(0 : ℝ), (F t)⁻¹ :=
      intervalIntegral.intervalIntegral_pos_of_pos
        (hcontinuous.intervalIntegrable z 0)
          (fun x => inv_pos.mpr (hpositive x)) hzneg
    rw [primitiveInv, intervalIntegral.integral_symm]
    linarith
  · exact (primitiveInv_pos_of_pos F hF hpositive hzpos).ne'

/-- The accumulated axial factor is nonzero away from the axis when `k = α + 2β` is nonzero. -/
theorem axialGamma_ne_zero_of_nonzero
    (alpha beta : ℝ) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (hk : alpha + 2 * beta ≠ 0)
    {z : ℝ} (hz : z ≠ 0) :
    axialGamma alpha beta F z ≠ 0 := by
  rw [axialGamma]
  exact mul_ne_zero (mul_ne_zero hk (hpositive z).ne')
    (primitiveInv_ne_zero_of_ne_zero F hF hpositive hz)

/-- The accumulated axial factor has the derivative obtained by the product rule. -/
theorem hasDerivAt_axialGamma
    (alpha beta : ℝ) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (z : ℝ) :
    HasDerivAt (axialGamma alpha beta F)
      ((alpha + 2 * beta) * deriv F z * primitiveInv F z +
        (alpha + 2 * beta) * F z * (F z)⁻¹) z := by
  have hFderiv : HasDerivAt F (deriv F z) z := by
    apply DifferentiableAt.hasDerivAt
    exact (hF.of_le (by norm_num)).differentiable_one z
  have hI := hasDerivAt_primitiveInv F hF hpositive z
  change HasDerivAt (fun y : ℝ =>
    (alpha + 2 * beta) * F y * primitiveInv F y)
    ((alpha + 2 * beta) * deriv F z * primitiveInv F z +
      (alpha + 2 * beta) * F z * (F z)⁻¹) z
  have hprod := (hFderiv.const_mul (alpha + 2 * beta)).mul hI
  have hfun : ((fun y : ℝ => (alpha + 2 * beta) * F y) * primitiveInv F) =
      (fun y : ℝ => (alpha + 2 * beta) * (F y * primitiveInv F y)) := by
    funext y
    simp only [Pi.mul_apply]
    ring
  rw [hfun] at hprod
  simpa only [mul_assoc] using hprod

/-- The exact derivative of `W = Γ - β z`. -/
theorem hasDerivAt_axialW
    (alpha beta : ℝ) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (z : ℝ) :
    HasDerivAt (axialW alpha beta F)
      ((alpha + 2 * beta) * deriv F z * primitiveInv F z +
        (alpha + 2 * beta) * F z * (F z)⁻¹ - beta) z := by
  have hgamma := hasDerivAt_axialGamma alpha beta F hF hpositive z
  have hid : HasDerivAt id 1 z := hasDerivAt_id z
  change HasDerivAt (fun y : ℝ => axialGamma alpha beta F y - beta * y)
    ((alpha + 2 * beta) * deriv F z * primitiveInv F z +
      (alpha + 2 * beta) * F z * (F z)⁻¹ - beta) z
  have hsub := hgamma.sub (hid.const_mul beta)
  have hfun : axialGamma alpha beta F - (fun y : ℝ => beta * id y) =
      (fun y : ℝ => axialGamma alpha beta F y - beta * y) := by
    funext y
    rfl
  rw [hfun] at hsub
  simpa only [mul_one] using hsub

/-- The primitive construction satisfies the axial identity on every point. -/
theorem axialW_axis_identity
    (alpha beta : ℝ) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (z : ℝ) :
    (axialW alpha beta F z + beta * z) * deriv F z +
      (alpha + beta - deriv (axialW alpha beta F) z) * F z = 0 := by
  have hFderiv : HasDerivAt F (deriv F z) z := by
    apply DifferentiableAt.hasDerivAt
    exact (hF.of_le (by norm_num)).differentiable_one z
  have hW := (hasDerivAt_axialW alpha beta F hF hpositive z).deriv
  rw [hW]
  simp only [axialW, axialGamma]
  field_simp [hpositive z |>.ne']
  ring

/-- The primitive for the derivative of an auxiliary axial profile. -/
def axialJ (A F : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..z, deriv A t / F t

/-- The off-axis pressure profile produced by the primitive. -/
def axialH (alpha beta : ℝ) (A F : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z = 0 then 0 else
    F z * axialJ A F z / (2 * axialGamma alpha beta F z)

/-- Off-axis pressure compatibility, with the actual derivative of the displayed primitive. -/
theorem axialH_pressure_compatibility
    (alpha beta : ℝ) (A F : ℝ → ℝ)
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (z : ℝ)
    (hz : z ≠ 0) (hgamma : axialGamma alpha beta F z ≠ 0) :
    HasDerivAt (axialH alpha beta A F)
      (((deriv F z * axialJ A F z + F z * (deriv A z / F z)) *
          (2 * axialGamma alpha beta F z) -
        (F z * axialJ A F z) *
          (2 * ((alpha + 2 * beta) * deriv F z * primitiveInv F z +
            (alpha + 2 * beta) * F z * (F z)⁻¹))) /
        (2 * axialGamma alpha beta F z) ^ 2) z := by
  have hFderiv : HasDerivAt F (deriv F z) z := by
    apply DifferentiableAt.hasDerivAt
    exact (hF.of_le (by norm_num)).differentiable_one z
  have hJ : HasDerivAt (axialJ A F) (deriv A z / F z) z := by
    have hquot : ContDiff ℝ 1 (fun t : ℝ => deriv A t / F t) := by
      have hAd : ContDiff ℝ 1 (deriv A) := by
        exact hA.deriv' (n := 1)
      exact hAd.div (hF.of_le (by norm_num)) (fun x => (hpositive x).ne')
    change HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, deriv A t / F t)
      (deriv A z / F z) z
    exact intervalIntegral.integral_hasDerivAt_right
        (hquot.continuous.intervalIntegrable (0 : ℝ) z)
        hquot.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hquot.continuous.continuousAt
  have hgammaDeriv := hasDerivAt_axialGamma alpha beta F hF hpositive z
  have hden : (2 * axialGamma alpha beta F) z ≠ 0 := by
    exact mul_ne_zero (by norm_num) hgamma
  have hquotient := (hFderiv.mul hJ).div (hgammaDeriv.const_mul 2) (by
    simpa [mul_comm] using hden)
  have hne : {y : ℝ | y ≠ 0} ∈ 𝓝 z :=
    compl_singleton_mem_nhds_iff.mpr hz
  have hEq : axialH alpha beta A F =ᶠ[𝓝 z]
      (F * axialJ A F / (fun y => 2 * axialGamma alpha beta F y)) := by
    filter_upwards [hne] with y hy
    simp [axialH, hy, Pi.div_apply]
  have hconverted := hquotient.congr_of_eventuallyEq hEq
  simpa only [Pi.mul_apply] using hconverted

/-- The displayed off-axis pressure primitive satisfies the axial compatibility identity. -/
theorem axialH_pressure_compatibility_identity
    (alpha beta : ℝ) (A F : ℝ → ℝ)
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (z : ℝ)
    (hz : z ≠ 0) (hgamma : axialGamma alpha beta F z ≠ 0) :
    axialGamma alpha beta F z * deriv (axialH alpha beta A F) z +
      (alpha + 2 * beta) * axialH alpha beta A F z = deriv A z / 2 := by
  have hderiv := (axialH_pressure_compatibility alpha beta A F hA hF
    hpositive z hz hgamma).deriv
  rw [hderiv]
  simp only [axialH, if_neg hz, axialGamma]
  have hki : (alpha + 2 * beta) * primitiveInv F z ≠ 0 := by
    intro hzero
    apply hgamma
    rw [axialGamma]
    calc
      (alpha + 2 * beta) * F z * primitiveInv F z =
          F z * ((alpha + 2 * beta) * primitiveInv F z) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  field_simp [hpositive z |>.ne', hki]
  apply (div_eq_iff hki).2
  ring

/-- The off-axis identity with the nonzero denominator discharged from positivity and `k ≠ 0`. -/
theorem axialH_pressure_compatibility_identity_of_nonzero
    (alpha beta : ℝ) (A F : ℝ → ℝ)
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (hk : alpha + 2 * beta ≠ 0)
    (z : ℝ) (hz : z ≠ 0) :
    axialGamma alpha beta F z * deriv (axialH alpha beta A F) z +
      (alpha + 2 * beta) * axialH alpha beta A F z = deriv A z / 2 :=
  axialH_pressure_compatibility_identity alpha beta A F hA hF hpositive z hz
    (axialGamma_ne_zero_of_nonzero alpha beta F hF hpositive hk hz)

#print axioms hasDerivAt_primitiveInv
#print axioms axialW_axis_identity
#print axioms axialH_pressure_compatibility
#print axioms axialH_pressure_compatibility_identity
#print axioms axialH_pressure_compatibility_identity_of_nonzero

end Soma.Holonics.Millennium.NavierStokesAxialPrimitive
