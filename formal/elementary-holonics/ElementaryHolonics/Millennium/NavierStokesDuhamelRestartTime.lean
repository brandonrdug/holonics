import ElementaryHolonics.Millennium.NavierStokesDuhamelKernelIntegral

/-!
# An explicit positive time aperture for the quadratic Duhamel contraction

The singular heat kernel has already returned an exact finite majorant.  This owner chooses one
positive time scale on which a nonnegative quadratic load makes the corresponding contraction
factor strictly smaller than one.  The scale shrinks by changing the same time aperture; no retry
bound or finite Fourier population is introduced.
-/

noncomputable section

open MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesDuhamelRestartTime

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral

/-- A positive reciprocal scale adapted simultaneously to viscosity and quadratic load. -/
def duhamelRestartScale (nu load : ℝ) : ℝ :=
  (16 * (1 + nu) * (1 + load))⁻¹

/-- The corresponding viscous time aperture. -/
def duhamelRestartTime (nu load : ℝ) : ℝ :=
  2 * nu * duhamelRestartScale nu load ^ 2

theorem duhamelRestartScale_pos
    {nu load : ℝ} (hnu : 0 < nu) (hload : 0 ≤ load) :
    0 < duhamelRestartScale nu load := by
  unfold duhamelRestartScale
  positivity

theorem duhamelRestartTime_pos
    {nu load : ℝ} (hnu : 0 < nu) (hload : 0 ≤ load) :
    0 < duhamelRestartTime nu load := by
  unfold duhamelRestartTime
  positivity [duhamelRestartScale_pos hnu hload]

/-- At the selected time, the square-root singularity reads exactly the reciprocal scale. -/
theorem sqrt_restartTime_div_two_nu
    {nu load : ℝ} (hnu : 0 < nu) (hload : 0 ≤ load) :
    Real.sqrt (duhamelRestartTime nu load / (2 * nu)) =
      duhamelRestartScale nu load := by
  have hnuNe : nu ≠ 0 := hnu.ne'
  have hscaleNonneg : 0 ≤ duhamelRestartScale nu load :=
    (duhamelRestartScale_pos hnu hload).le
  rw [duhamelRestartTime]
  have hquotient :
      2 * nu * duhamelRestartScale nu load ^ 2 / (2 * nu) =
        duhamelRestartScale nu load ^ 2 := by
    field_simp
  rw [hquotient, Real.sqrt_sq hscaleNonneg]

/-- The explicit scalar factor multiplying the quadratic path difference is strictly below one. -/
theorem two_load_mul_restartKernelBound_lt_one
    {nu load : ℝ} (hnu : 0 < nu) (hload : 0 ≤ load) :
    2 * load *
        (duhamelRestartTime nu load +
          2 * Real.sqrt (duhamelRestartTime nu load / (2 * nu))) < 1 := by
  let r := duhamelRestartScale nu load
  have hr : 0 < r := duhamelRestartScale_pos hnu hload
  have hnuOne : nu < 1 + nu := by linarith
  have hloadOne : load < 1 + load := by linarith
  have hden : 0 < 16 * (1 + nu) * (1 + load) := by positivity
  have hrEq : r = (16 * (1 + nu) * (1 + load))⁻¹ := rfl
  have hloadr : load * r < 1 / 16 := by
    rw [hrEq, inv_eq_one_div]
    rw [mul_one_div]
    apply (div_lt_iff₀ hden).2
    have hnuPos : 0 < 1 + nu := by linarith
    nlinarith [mul_lt_mul_of_pos_left hloadOne hnuPos]
  have hnur : nu * r < 1 / 16 := by
    rw [hrEq, inv_eq_one_div]
    rw [mul_one_div]
    apply (div_lt_iff₀ hden).2
    have hloadPos : 0 < 1 + load := by linarith
    nlinarith [mul_lt_mul_of_pos_right hnuOne hloadPos]
  have hfirst : 4 * load * nu * r ^ 2 < 1 / 64 := by
    have hgapLoad : 0 < 1 / 16 - load * r := sub_pos.mpr hloadr
    have hgapNu : 0 < 1 / 16 - nu * r := sub_pos.mpr hnur
    have hproduct := mul_pos hgapLoad hgapNu
    have hloadrNonneg : 0 ≤ load * r := mul_nonneg hload hr.le
    have hnurNonneg : 0 ≤ nu * r := mul_nonneg hnu.le hr.le
    nlinarith [mul_nonneg hloadrNonneg hnurNonneg]
  have hsecond : 4 * load * r < 1 / 4 := by nlinarith
  rw [sqrt_restartTime_div_two_nu hnu hload]
  change 2 * load * (2 * nu * r ^ 2 + 2 * r) < 1
  nlinarith

/-- The actual integrated heat majorant at the selected aperture inherits the strict contraction
bound. -/
theorem two_load_mul_integral_duhamelHeatKernel_lt_one
    {nu load : ℝ} (hnu : 0 < nu) (hload : 0 ≤ load) :
    2 * load *
        (∫ tau in (0 : ℝ)..duhamelRestartTime nu load,
          duhamelHeatKernelMajorant nu tau) < 1 := by
  have htime := duhamelRestartTime_pos hnu hload
  have hintegral := intervalIntegral_duhamelHeatKernelMajorant_le hnu htime
  have hfactor : 0 ≤ 2 * load := mul_nonneg (by norm_num) hload
  exact (mul_le_mul_of_nonneg_left hintegral hfactor).trans_lt
    (two_load_mul_restartKernelBound_lt_one hnu hload)

section Audit

#print axioms sqrt_restartTime_div_two_nu
#print axioms two_load_mul_restartKernelBound_lt_one
#print axioms two_load_mul_integral_duhamelHeatKernel_lt_one

end Audit

end Soma.Holonics.Millennium.NavierStokesDuhamelRestartTime
